using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Runtime.Serialization;
using System.ServiceModel;
using System.Text;
using System.Text.RegularExpressions;
using System.Windows.Forms;
using System.Diagnostics;
using FileImage;
using System.Management;
using IMAPI2.Interop;
using System.IO;
using System.Net;
using System.Configuration;
using ISOFileImage;
using Itenso.TimePeriod;
using System.Threading;
using System.Globalization;


using SRIPArchiveClientToolsForm.Properties;
using TZ = TimezoneFunctions;
using CTI.emPulse.Business;
//
// place all strings in resource files - 
// simplify I18N transition...
//
using RES = SRIPArchiveClientToolsForm.Properties;
using Microsoft.Win32;
using ScreenRecordingExporter;
using Ionic.Utils.Zip;
using DiscUtils.Iso9660;
using DiscUtils.Udf;


//
// Use ws instead of wcf...
//
using ArchiveWS = SRIPArchiveClientToolsForm.ArchiveWebRefClassic.ArchiveWS;
using ArchiveData = SRIPArchiveClientToolsForm.ArchiveWebRefClassic.ArchiveData;
using RecordedCalls = SRIPArchiveClientToolsForm.ArchiveWebRefClassic.RecordedCalls;
using ScreenRecordingForArchival = SRIPArchiveClientToolsForm.ArchiveWebRefClassic.ScreenRecordingForArchival;

namespace SRIPArchiveClientToolsForm
{
    public partial class SRIPArchiveClientForm : Form
    {
        #region Properties...
        //////////////////////////////////////////////////////////////////////////        
        public FileImageInfo ObjFileImageInfo { get; set; }

        public RecordedCalls[] CallsArray { get; set; }

        public RecordedCalls[] RecycleBinCallsArray { get; set; }

        public List<SearchField> SearchFieldData { get; set; }

        public ScreenRecordingForArchival[] ScreenRecordingVideoArray { get; set; }

        static int _numberOfProcessorsAvailable = -1;
        public static int NumberOfProcessorsAvailable
        {
            get
            {
                if (_numberOfProcessorsAvailable == -1)
                    _numberOfProcessorsAvailable = GetAffinitizedProcessorCount();
                return _numberOfProcessorsAvailable;
            }
        }

        /// <summary>
        /// added for download performance tweaks
        /// </summary>
        public static int NumberOfCPUs
        {
            get { return _numberOfCPUs; }
            set { _numberOfCPUs = value; }
        }
        /// <summary>
        /// added for download performance tweaks
        /// </summary>
        public static int NumberOfCPUConnections
        {
            get { return _numberOfCPUConnections; }
            set { _numberOfCPUConnections = value; }
        }
        /// <summary>
        /// what's in the ConnectionLimit var...
        /// </summary>
        public static int RequestedConnectionLimit { get; set; }

        /// <summary>
        /// use an instance of a asmx web service
        /// instead of a wcf web service...
        /// </summary>
        public static ArchiveWS ClassicArchiveWS
        {
            get
            {
                return new ArchiveWS
                {
                    Url = _callRecordingURL + ArchiveWebServiceURLPostPend()
                };
            }
        }
        //////////////////////////////////////////////////////////////////////////        
        #endregion

        #region Fields...
        //////////////////////////////////////////////////////////////////////////                    
        Stopwatch _timeRemainingEstimates = new Stopwatch();
        Stopwatch _elapsedIsoCreationTime = new Stopwatch();
        Stopwatch _elapsedFileDownloadIsoCreationTime = new Stopwatch();
        Stopwatch _elapsedFileDownloadTime = new Stopwatch();
        ImageRepository _imageRepository;
        static readonly object _objectLock = new object();
        BackgroundWorker _bgWorkerAddFilesToImageRepository = new BackgroundWorker();

        /// <summary>
        /// Note: 
        /// AutoResetEvent is like a ticket turnstile in a subway: inserting a ticket
        /// lets exactly one person through. "Auto" refers to the fact that an open
        /// turnstile automatically closes or "resets" after someone steps through.
        /// So a thread waits or blocks at the turnstile by calling "WaitOne"
        /// (wait at this "one" turnstile until it opens). The turnstile is opened
        /// when a ticket is inserted (someone calling "Set"). It is important
        /// to note that if a number of threads have called "WaitOne", a
        /// queue builds up at the turnstile; so, depending on the environment, the
        /// fairness of the queue can sometimes be violated...
        /// </summary>      
        static AutoResetEvent _autoEventMultiFileDownload = new AutoResetEvent(false);
        static AutoResetEvent _autoEventMaxMultiFileDownloadExceeded = new AutoResetEvent(false);
        static AutoResetEvent _autoEventZeroByteFileDownload = new AutoResetEvent(false);
        static AutoResetEvent _autoEventFixZeroByteFileDownloadNoISO = new AutoResetEvent(false);
        static AutoResetEvent _autoEventLoadAudioVideoFileInGrid = new AutoResetEvent(false);
        static AutoResetEvent _autoEventAllSQLDataRetrieved = new AutoResetEvent(false);
        static AutoResetEvent _autoEventAllAudioFilesDownloaded = new AutoResetEvent(false);
        static AutoResetEvent _autoEventCreateIsoImageRepository = new AutoResetEvent(false);
        static AutoResetEvent _autoEventRetrieveSqlResultSetInChunks = new AutoResetEvent(false);
        static AutoResetEvent _autoEventIsoWriterWorking = new AutoResetEvent(false);
        static AutoResetEvent _autoEventIsoWriterCriticalLoop = new AutoResetEvent(false);
        static AutoResetEvent _autoEventCdBuilderStartIsoCreation = new AutoResetEvent(false);
        static AutoResetEvent _autoEventCdBuilderIsoCreationInProgress = new AutoResetEvent(false);


        static string _msgs = string.Empty;
        static string _appName = Application.ProductName;
        static string _bgWorkerErrorMsgs = string.Empty;

        static string _isoDirectoryLayout = ConfigurationManager.AppSettings["ISODirectoryLayout"];
        static string _outputISOFileName = ConfigurationManager.AppSettings.Get("OutputISOFileName");
        static string _callRecordingURL = ConfigurationManager.AppSettings["ARCURL"];
        static string _userName = ConfigurationManager.AppSettings["UserName"];
        static string _outputLocation = ConfigurationManager.AppSettings["OutputLocation"];
        static string _mediaVolumeName = ConfigurationManager.AppSettings["MediaVolumeName"];
        static string _isoReaderOutputLocation = ConfigurationManager.AppSettings["ISOViewerOutputLocation"];
        static string _audioExtensionConfigItem = ConfigurationManager.AppSettings["AudioExtensionList"];
        static string _validFileExtensionsConfigItem = ConfigurationManager.AppSettings["ValidFileExtensions"];

        #region Configuration variables with default settings...
        ////////////////////////////////////////////////////////////////////////// 
        static int _tzIndex = (int.TryParse(ConfigurationManager.AppSettings["TZIndex"].ToString()
                , out _tzIndex)) ? _tzIndex : 0;
        static int _maxNumberOfFilesToDownloadConcurrently = (int.TryParse(ConfigurationManager.AppSettings["MaxNumberFilesToDownloadAtOnce"]
            , out _maxNumberOfFilesToDownloadConcurrently)) ? _maxNumberOfFilesToDownloadConcurrently : 9;
        static long _overrideFormatMaxSize = (long.TryParse(ConfigurationManager.AppSettings["OverrideFormatFileSize"]
            , out _overrideFormatMaxSize)) ? _overrideFormatMaxSize : 0;
        static int _maxAttemptsToContactServer = (int.TryParse(ConfigurationManager.AppSettings["MaxAttemptsToUpdateDB"]
            , out _maxAttemptsToContactServer)) ? _maxAttemptsToContactServer : 7;
        static int _isoFileFormatType = (int.TryParse(ConfigurationManager.AppSettings["ISOFileFormat"]
            , out _isoFileFormatType)) ? _isoFileFormatType : 0;

        static bool _includeArchivedCalls = (bool.TryParse(ConfigurationManager.AppSettings["IncludeArchivedCalls"], out _includeArchivedCalls)) && _includeArchivedCalls;
        static bool _archiveRecycleBinContents = (bool.TryParse(ConfigurationManager.AppSettings["ArchiveRecycleBin"], out _archiveRecycleBinContents)) && _archiveRecycleBinContents;
        static DateTime _getStartDate = (DateTime.TryParse(ConfigurationManager.AppSettings["StartDate"]
            , out _getStartDate)) ? _getStartDate : DateTime.Now;
        static DateTime _getEndDate = (DateTime.TryParse(ConfigurationManager.AppSettings["EndDate"]
            , out _getEndDate)) ? _getEndDate : DateTime.Now;
        static long _maxReceivedMsgSize = (long.TryParse(ConfigurationManager.AppSettings["MaxReceivedMsgSize"]
            , out _maxReceivedMsgSize)) ? _maxReceivedMsgSize : 2147483647;
        static bool _maintainWindowPosition = (bool.TryParse(ConfigurationManager.AppSettings["MaintainWindowPosition"], out _maintainWindowPosition)) && _maintainWindowPosition;
        static bool _doNotCreateISOImage = (bool.TryParse(ConfigurationManager.AppSettings["DoNotCreateISO"], out _doNotCreateISOImage)) && _doNotCreateISOImage;
        static bool _doNotUpdateArchiveDbTables = (bool.TryParse(ConfigurationManager.AppSettings["DoNotUpdateArchiveDbTables"], out _doNotUpdateArchiveDbTables)) && _doNotUpdateArchiveDbTables;
        static bool _doNotDownloadVideoFiles = (bool.TryParse(ConfigurationManager.AppSettings["DoNotDownloadVideoFiles"], out _doNotDownloadVideoFiles)) && _doNotDownloadVideoFiles;
        static bool _doNotDeleteDownloadedFiles = (bool.TryParse(ConfigurationManager.AppSettings["SaveDownloadedFiles"], out _doNotDeleteDownloadedFiles)) && _doNotDeleteDownloadedFiles;
        static int _numberOfCPUs = (int.TryParse(ConfigurationManager.AppSettings["NumberOfCPUs"]
            , out _numberOfCPUs)) ? _numberOfCPUs : 1;
        static int _numberOfCPUConnections = (int.TryParse(ConfigurationManager.AppSettings["NumberOfCPUConnection"]
            , out _numberOfCPUConnections)) ? _numberOfCPUConnections : 1;
        //////////////////////////////////////////////////////////////////////////        
        #endregion

        static string _startDate = _getStartDate.ToString();
        static string _endDate = _getEndDate.ToString();
        static string _isoReaderInputFile = string.Empty;
        static string _currentTimeZoneSelected = string.Empty;
        static string _password = string.Empty;
        static string _strSelectAll = "Select All";
        static string _strSelectNone = "Select None";
        static string _contentsForVolumeName = _mediaVolumeName; //Bug #3602: show vol name on viewer page

        string _holdFormattingMsg = string.Empty;
        string _holdUpdatingMsg = string.Empty;

        static bool _udfFileSystemRequired = false;

        /// <summary>
        /// 2GB - 2,147,483,648L
        /// </summary>
        private const long _udfRequiredSingleFileSize = 2147483648L;

        /// <summary>
        /// 8.5GB - 9,126,805,504L
        /// </summary>
        private const long _maxUDFFormatFileSize = 9126805504L;

        /// <summary>
        /// 4.69GB - 5,044,489,420L
        /// </summary>
        private const long _maxJolietFormatFileSize = 5044489420L; //5046586572L; 

        /// <summary>
        /// 698MB - 731,906,048L
        /// </summary>
        private const long _maxCDFormatFileSize = 731906048L; //734003200L   

        /// <summary>
        /// 4.696GB - 5,042,392,268L
        /// </summary>
        private const long _maxDVDFormatFileSize = 5042392268L; //5044489420L;

        static long _formatFileSize = 0;


        long _freeSpace = 0;
        long _hdSize = 0;
        int _totalTasksToProcess = 0;
        int _totalTasksProcessed = 0;
        int _nrOfRowsSelected = 0;

        #region Stuff we added for multiple iso file creation...
        //////////////////////////////////////////////////////////////////////////        
        static long _downloadFileSizeRunningTotal = 0;
        static int _isoImageRepositoryIndex = 0; // increment as we add new images
        static int _isoIterateImageRepository = 0; // increment as we extract those images
        List<ImageRepository> _imageRepositoryList = new List<ImageRepository>(); // throw everybody in the list        
        static DateTime _holdDateTimeForName = DateTime.Now;
        static Dictionary<int, List<FileImageInfo.ArchiveData>> _dictionaryOfArchiveDataTableContent
                    = new Dictionary<int, List<FileImageInfo.ArchiveData>>();
        static int _callsToDownLoadCount = 0;
        static int _videosToDownLoadCount = 0;
        static int _initialCountOfCallsToDownLoad = 0;
        static int _currentDownloadFileCount = 0;
        static readonly object _downloadPadLock = new object();
        static List<string> _transportErrors = new List<string>();
        static readonly object _createIndexNameLock = new object();
        static readonly object _writeIndexContentLock = new object();
        static readonly object _trackDownloadFileSizeAccum = new object();
        static readonly object _verifyingContentWillFitOnImage = new object();
        static int _countOfAudioWithNoRecordingFileLocation = 0;
        static int _countOfScreenRecordingWithNoRecordingFileLocation = 0;
        //////////////////////////////////////////////////////////////////////////        
        #endregion

        static bool _cancellationPendingWebService = false;
        static bool _cancellationWebServiceError = false;
        static bool _cancelledCOMRunTimeError = false;
        static bool _filesNotFoundError = false;
        static bool _arcDownLoadTimeOutError = false;
        static bool _safeToDeleteTempDirectory = false;
        static bool _selectAllRows = false;
        static bool _cancellationPendingAddingFilesToImageRepository = true;
        static bool _cancellationISOWriter = false;
        static bool _showStartUpMsg = true;

        #region Stuff we added for downloading something other than an MP3 file...
        //////////////////////////////////////////////////////////////////////////
        static List<string> _audioExtensionList = new List<string>();
        static List<string> _validFileExtensionsList = new List<string>();
        static int _totalNumberOfVideoFilesToDownload = 0;
        static int _saveMaxNumberOfFilesToDownloadConcurrently = 0;
        static int _saveNumberOfCPUs = 0;
        //////////////////////////////////////////////////////////////////////////
        #endregion

        #region Stuff we added for updating timezone files...
        //////////////////////////////////////////////////////////////////////////
        static List<string> _timeZoneDirectoryExclusionList = new List<string>();
        //////////////////////////////////////////////////////////////////////////
        #endregion

        #region Stuff we added for requesting sql result set in hourly chunks...
        //////////////////////////////////////////////////////////////////////////
        private const int OneSecond = 1000;
        private const int ChunkRetryWaitTimeInMilliseconds = (int)(OneSecond * .05); // set to 50ms
        private const int ChunkRetryLimit = OneSecond / ChunkRetryWaitTimeInMilliseconds;
        static int _archiveNumberOfDaysLimit = (int.TryParse(ConfigurationManager.AppSettings["ArchiveNumberOfDaysLimit"]
            , out _archiveNumberOfDaysLimit)) ? _archiveNumberOfDaysLimit : 90;
        //////////////////////////////////////////////////////////////////////////
        #endregion

        //////////////////////////////////////////////////////////////////////////        
        #endregion

        #region Nested Types...
        //////////////////////////////////////////////////////////////////////////   

        /// <summary>
        /// 
        /// </summary>
        public class LaunchVideoFileObject
        {
            public DataGridViewCellEventArgs GridViewCellEvent { get; set; }
            public string VideoFileName { get; set; }
        }

        /// <summary>
        /// 
        /// </summary>
        public class ZeroByteFileHandlerObject
        {
            public FileImageInfo.IndexData IndexData { get; set; }
        }
        /// <summary>
        /// 
        /// </summary>
        public class ZeroByteFileHandlerForNoISOImageObject
        {
            public FileImageInfo _ObjFileImageInfo { get; set; }
            public int _FileCount { get; set; }
        }
        /// <summary>
        /// default object for passing data to
        /// progress workers
        /// </summary>
        public class ObjProgressInfo
        {
            public string _fileName;
            public int _recCount;
            public long _fileSize;
            public int _filesRemaining;
            public bool _startup;
            public bool _completed;
        }
        /// <summary>
        /// support Viewer search
        /// </summary>
        public class SearchField
        {
            public string DataPropertyName { get; set; }
            public string FriendlyName { get; set; }
            public int Index { get; set; }
        }

        /// <summary>
        /// support threaded download of 
        /// an MP3, SRF, etc.. 
        /// </summary>
        public class DownLoadFileObject
        {
            public BackgroundWorker _bgWorkerWebServiceMP3;
            public FileImageInfo _objFileImageInfo;
            public int _totalWeDownloadedSuccessfully;
            public ObjProgressInfo _objPI;
            public RecordedCalls _rc;
            public string _downLoadPath;
            public string _recordingLinkURL;
            public ScreenRecordingForArchival _srfa;

            /// <summary>
            /// added so that we only store MP3 data
            /// if the call successfully downloaded; 
            /// it may be reasonable to test for calls
            /// with 0 bytes, but since the call may
            /// in fact have 0 bytes we will not exclude
            /// it if this method is called...
            /// </summary>
            /// <param name="objPI"></param>
            /// <param name="rc"></param>
            /// <param name="downLoadPath"></param>
            /// <param name="ObjFileImageInfo"></param>
            public bool StoreFileDownLoadResults(DownLoadFileObject dObj)
            {
                bool results = true;
                string videoDownloadPathAndName = string.Empty;
                try
                {
                    if (dObj._objFileImageInfo.PathsAndFileNames.Contains(dObj._downLoadPath))
                    {
                        Log.LogWrite("StoreFileDownLoadResults(): dObj._objFileImageInfo.PathsAndFileNames already contains " + dObj._downLoadPath);
                        return false;
                    }

                    // 1. name and location of recordings...
                    dObj._objFileImageInfo.PathsAndFileNames.Add(dObj._downLoadPath);

                    if (_doNotDownloadVideoFiles.Equals(false))
                    {
                        // 1a. name and location of screen videos...
                        if (!string.IsNullOrEmpty(dObj._srfa.RecordingFileLocation))
                        {
                            videoDownloadPathAndName =
                                new FileInfo(dObj._downLoadPath).DirectoryName
                                + "\\"
                                + new FileInfo(dObj._srfa.RecordingFileLocation).Name;
                            //
                            // always add this info to the list of MP3's, SRF's, etc.
                            // that will be burned to ISO image later
                            dObj._objFileImageInfo.PathsAndFileNames.Add(videoDownloadPathAndName);
                        }
                    }


                    // 2. save entries for archive table update

                    dObj._objFileImageInfo.ArchiveTableList.Add(new FileImageInfo.ArchiveData
                    {
                        CallId = dObj._rc.CallID
                        ,
                        MP3DownLoadPathAndFileName = dObj._downLoadPath
                        ,
                        UserName = dObj._objFileImageInfo.UserName
                        ,
                        CallDateTime = dObj._rc.CallTime
                        ,
                        ArchiveFileName =
                            dObj._objFileImageInfo.ArchiveFileName
                        ,
                        SRFDownLoadPathAndFileName =
                            videoDownloadPathAndName
                            // added new file type for download...
                        ,
                        ScrRecordingID = dObj._srfa.RecordingId
                    });

                    // 3a. save csv content 
                    dObj._objFileImageInfo.IndexFileData.Add(new FileImageInfo.IndexData
                    {
                        CallID = dObj._rc.CallID
                        ,
                        RecordedFileName = dObj._downLoadPath
                        ,
                        UserName = dObj._objFileImageInfo.UserName
                        ,
                        CallDateTime = dObj._rc.CallTime
                        ,
                        ExtnNumber = dObj._rc.ExtnNumber
                        ,
                        FromNumber = dObj._rc.FromNumber
                        ,
                        ToNumber = dObj._rc.ToNumber
                        ,
                        Comments = dObj._rc.Comments
                        ,
                        ExtensionId = dObj._rc.ExtensionId
                        ,
                        Location = dObj._rc.Location
                        ,
                        Md5Hash = dObj._rc.MD5Hash
                        ,
                        Duration = dObj._rc.Duration
                        ,
                        DiskSize = dObj._rc.DiskSize
                        ,
                        DirectionFlag = dObj._rc.DirectionFlag
                        ,
                        FromCallerID = dObj._rc.FromCallerID
                        ,
                        ToCallerID = dObj._rc.ToCallerID
                        ,
                        LocLookupDisplay = string.Empty
                        ,
                        Selected = false
                        ,
                        // 
                        // SRF Files...
                        // extend IndexFileData here for new file type being saved to ISO image...
                        //
                        VideoFileName = videoDownloadPathAndName
                        ,
                        RecordingId = dObj._srfa.RecordingId
                        ,
                        AudioPosition = dObj._srfa.AudioPosition
                        ,
                        StartPos = dObj._srfa.StartPos
                        ,
                        EndPos = dObj._srfa.EndPos
                        ,
                        RecordingGuid = dObj._srfa.RecordingGuid
                    });
                }
                catch (Exception ex)
                {
                    UpdateEventViewer(_appName, ex.Message, EventLogEntryType.Warning);
                    results = false;
                }

                return results;
            }

            /// <summary>
            /// 
            /// </summary>
            /// <param name="eventMsg"></param>
            /// <param name="logEntryType"></param>
            public void UpdateEventViewer(string appName, string eventMsg, EventLogEntryType logEntryType)
            {
                Log.LogWrite(eventMsg);
                EventLog.WriteEntry(appName, eventMsg, logEntryType);
            }
        }
        //////////////////////////////////////////////////////////////////////////        
        #endregion

        #region Events...
        //////////////////////////////////////////////////////////////////////////        
        event ImageRepository.CancelingHandler Stop;
        //////////////////////////////////////////////////////////////////////////        
        #endregion

        #region Delegates...
        //////////////////////////////////////////////////////////////////////////        
        static DownloadProgressChangedEventHandler _downloadProgressChangedHandler;
        static AsyncCompletedEventHandler _downloadFileCompletedHandler;
        //////////////////////////////////////////////////////////////////////////        
        #endregion

        #region Enums...
        //////////////////////////////////////////////////////////////////////////
        /// <summary>
        /// 
        /// </summary>
        enum ISOFileType
        {
            CD = 0,
            DVD,
            UDF
        }

        enum SupportedDownloadFileTypes
        {
            MP3 = 0,
            SRF,
        }
        //////////////////////////////////////////////////////////////////////////
        #endregion




        #region Phase 0 - Initialization...
        //////////////////////////////////////////////////////////////////////////

        /// <summary>
        /// ctor
        /// </summary>
        public SRIPArchiveClientForm()
        {
            InitializeComponent();

            try
            {
                Log.TaskLogPath = Application.ExecutablePath + "_" + DateTime.Now.ToString("s").Replace(":", "-") + ".log";
                Log.OpenLogger();
                Log.LogWrite("Entered Archive Client Tool...");

                CreateEventLogSource();

                // get environment data...
                GetEnvironmentData();

                _msgs = string.Format("Localize UI Items...");
                UpdateEventViewer(_msgs, EventLogEntryType.Information);
                LocalizeUIItems();

                _msgs = string.Format("Restore window position? {0}", _maintainWindowPosition.ToString());
                UpdateEventViewer(_msgs, EventLogEntryType.Information);
                if (_maintainWindowPosition)
                    RestoreWindow();

                _msgs = string.Format("Check timezone library availabiltiy...");
                UpdateEventViewer(_msgs, EventLogEntryType.Information);
                OlsonTimeZoneObject otzo = new OlsonTimeZoneObject();
                bool tzOk = otzo.OlsonTimeZoneFolderPopulated();

                _msgs = string.Format("Found timezone library? {0}", tzOk.ToString());
                UpdateEventViewer(_msgs, EventLogEntryType.Information);
                if (!tzOk)
                {
                    // shouldn't be here...                
                    MessageBox.Show("Timezone input file not found. Unable to continue...", "Error", MessageBoxButtons.OK, MessageBoxIcon.Error);
                    return;
                }
                // future...
                UpdateTimeZoneFiles();

                _downloadProgressChangedHandler = WcDownloadProgressChanged;
                _downloadFileCompletedHandler = WcDownloadFileCompleted;

                btnSelectAll.Visible = false;
                txtUserName.Text = _userName;
                txtPassword.PasswordChar = '*';

                comboBoxTimeZoneList.DataSource = PopulateTZList();

                comboBoxTimeZoneList.SelectedIndex =
                    (_tzIndex < 0) || (_tzIndex > comboBoxTimeZoneList.Items.Count - 1)
                    ? 0
                    : _tzIndex;

                try
                {
                    dtpStartDate.Value = !string.IsNullOrEmpty(_startDate) ?
                        Convert.ToDateTime(_startDate) :
                        DateTime.Now;
                    dtpEndDate.Value = !string.IsNullOrEmpty(_endDate) ?
                        Convert.ToDateTime(_endDate) :
                        DateTime.Now;

                    dtpStartTime.Value = !string.IsNullOrEmpty(_startDate) ?
                        new DateTime(dtpStartDate.Value.Year, dtpStartDate.Value.Month, dtpStartDate.Value.Day, dtpStartDate.Value.Hour, dtpStartDate.Value.Minute, dtpStartDate.Value.Second) :
                        new DateTime(dtpStartDate.Value.Year, dtpStartDate.Value.Month, dtpStartDate.Value.Day, 0, 0, 0);
                    dtpEndTime.Value = !string.IsNullOrEmpty(_endDate) ?
                        new DateTime(dtpEndDate.Value.Year, dtpEndDate.Value.Month, dtpEndDate.Value.Day, dtpEndDate.Value.Hour, dtpEndDate.Value.Minute, dtpEndDate.Value.Second) :
                        new DateTime(dtpEndDate.Value.Year, dtpEndDate.Value.Month, dtpEndDate.Value.Day, 23, 59, 59);
                }
                catch (Exception ex)
                {
                    //
                    // this most likely is an L10N error...
                    _msgs = string.Format(Resources.RES_ErrorSettingDefaultDateTime
                        , ex.Message
                        , ex.InnerException
                        , ex.StackTrace
                        , _startDate
                        , _endDate);

                    UpdateEventViewer(_msgs, EventLogEntryType.Warning);
                }

                chkBoxArchiveRecylceBin.Checked = _archiveRecycleBinContents;
                chkBoxIncludeArchivedCalls.Checked = _includeArchivedCalls;
                txtOutputLocation.Text = _outputLocation;
                txtMediaVolumeName.Text = _mediaVolumeName;
                txtMediaVolumeName.MaxLength = 29;

                // bug 4471: ArchiveTool default configuration setting for portal to https, not http
                if (_callRecordingURL.ToUpper().Contains(@"VALIDDOMAINNAMEREQUIREDHERE"))
                    _callRecordingURL = GetApplicationUrl(_callRecordingURL);

                // added to allow user way to select the
                // number of physical CPU on server - 
                // default to 1
                nudNumberOfCPUs.Minimum = 1;
                nudNumberOfCPUs.Maximum = NumberOfProcessorsAvailable; //4;
                nudNumberOfCPUs.Value = _numberOfCPUs;

                // added to allow user way to select the
                // number of max connections to open for
                // each CPU - default to 3
                nudConnections.Increment = 1;
                nudConnections.Minimum = 1;
                nudConnections.Maximum = 12;
                //nudConnections.Value = 3;

                // added to allow user way to select the
                // number of files to download simultaneously -
                // default to 2
                nudMultiFileDownload.Minimum = 1;
                nudMultiFileDownload.Maximum = 7; // don't open more than 7 WebClient objects at once?
                nudMultiFileDownload.Value = _maxNumberOfFilesToDownloadConcurrently;

                txtWebServiceURL.Text = _callRecordingURL;

                txtISODirectoryLayout.Text = _isoDirectoryLayout;
                txtCustomFileName.Text = _outputISOFileName;
                txtISOFileReaderOutputDir.Text = _isoReaderOutputLocation;

                // set max attempts to retry anything at 7...
                _maxAttemptsToContactServer = _maxAttemptsToContactServer > 7 ? 7 : _maxAttemptsToContactServer;

                // set basic formatting stuff...
                _formatFileSize = _maxCDFormatFileSize;
                switch ((ISOFileType)Enum.Parse(typeof(ISOFileType), _isoFileFormatType.ToString()))
                {
                    case ISOFileType.CD:
                        radioBtnCD.Checked = true;
                        break;
                    case ISOFileType.DVD:
                        radioBtnDVD.Checked = true;
                        break;
                    case ISOFileType.UDF:
                        radioBtnOther.Checked = true;
                        break;
                    default:
                        radioBtnCD.Checked = true;
                        break;
                }
                if (_overrideFormatMaxSize > 0 && _overrideFormatMaxSize < _formatFileSize)
                {
                    _formatFileSize = _overrideFormatMaxSize;
                }

                // poopulate controls on navigator we care about 
                _msgs = string.Format("Create ISO viewer support...");
                UpdateEventViewer(_msgs, EventLogEntryType.Information);
                AddGridviewFilterSupport();
                //
                // Bug #3601: ArchivalTool: Viewer display, default pop up 
                // directory path for input to where default save was at
                //
                // Fix: Add the path to the control and allow the user 
                //  to use the auto-suggest feature to find the specific file
                //
                txtISOFile.Text = new FileInfo(_outputLocation).DirectoryName;
                //
                // testing CSV x64 issues and option...
                //DataTable dt1, dt2;
                //dt1 = ParseCSVSimple("C:\\Temp\\ISO Files\\ViewerOutputLocation\\a_Index.csv");
                //dt2 = ParseCSVComplex("C:\\Temp\\ISO Files\\ViewerOutputLocation\\a_Index.csv");
                //

                // changes made for Larry Low @ Telesphere - 
                _transportErrors.Clear();
                btnCopyText.Enabled = false;

                chkBoxDoNotDownloadVideoFiles.Checked = _doNotDownloadVideoFiles;
                chkBoxDoNotCreateISOImage.Checked = _doNotCreateISOImage;
                chkBoxDoNotUpdateArchiveTables.Checked = _doNotUpdateArchiveDbTables;
                chkBoxDoNotDeleteDownloadedFiles.Checked = _doNotDeleteDownloadedFiles;

                //
                // remove since attempting to delete is a waste of time...
                //
                //chkBoxDoNotDeleteDownloadedFiles.Visible = false;

                // stuff we added for downloading video files...
                _audioExtensionList = _audioExtensionConfigItem.ToUpper().Split(';').ToList();
                _validFileExtensionsList = _validFileExtensionsConfigItem.ToUpper().Split(';').ToList();

                ApplyArcToolTips();
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                Log.LogWrite(_msgs);
            }
        }

        /// <summary>
        /// create tooltips for ARC controls...
        /// </summary>
        private void ApplyArcToolTips()
        {
            _arcToolTips.AutomaticDelay = 550;
            _arcToolTips.ShowAlways = true;
            //
            // Parameters Page...
            //
            _arcToolTips.SetToolTip(comboBoxTimeZoneList, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Select_Timezone_The_Data_Will_Belong_To_);
            _arcToolTips.SetToolTip(txtUserName, Resources.SRIPArchiveClientForm_ApplyArcToolTips_User_Name_With_Access_To_Data_);
            _arcToolTips.SetToolTip(txtPassword, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Password_For_The_User_);
            _arcToolTips.SetToolTip(dtpStartDate, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Search_For_Data_Beginning_At_This_Date_);
            _arcToolTips.SetToolTip(dtpStartTime, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Search_For_Date_Starting_At_This_Time_);
            _arcToolTips.SetToolTip(dtpEndDate, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Search_For_Data_Up_To_This_Date_);
            _arcToolTips.SetToolTip(dtpEndTime, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Search_For_Data_Up_To_This_Time_);
            _arcToolTips.SetToolTip(chkBoxArchiveRecylceBin, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Search_For_Data_In_Recycle_Bin_Only_);
            _arcToolTips.SetToolTip(chkBoxIncludeArchivedCalls, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Calls_That_Have_Been_Archived_Will_Be_Retrieved_);
            _arcToolTips.SetToolTip(txtOutputLocation, Resources.SRIPArchiveClientForm_ApplyArcToolTips_The_Location_Of_The_ISO_Image_);
            _arcToolTips.SetToolTip(txtMediaVolumeName, Resources.SRIPArchiveClientForm_ApplyArcToolTips_ISO_Internal_Media_Name_);
            _arcToolTips.SetToolTip(btnSaveLocation, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Select_Location_To_Save_The_ISO_Image_);
            _arcToolTips.SetToolTip(radioBtnCD, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Create_CD_Format_ISO_Image_);
            _arcToolTips.SetToolTip(radioBtnDVD, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Create_DVD_Format_ISO_Image_);
            _arcToolTips.SetToolTip(radioBtnOther, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Create_DVD_DL_Format_ISO_Image_);
            _arcToolTips.SetToolTip(btnCopyText, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Copies_All_Or_Selected_Data_From_The_Status_Window_To_The_Clipboard_);
            //
            // Configuration Page...
            //
            _arcToolTips.SetToolTip(txtWebServiceURL,Resources.SRIPArchiveClientForm_ApplyArcToolTips_URL_Where_Recordings_Are_Located_);
            _arcToolTips.SetToolTip(txtISODirectoryLayout, Resources.SRIPArchiveClientForm_ApplyArcToolTips_The_Directory_Structure_That_Will_Be_Used_On_The_ISO_Image_);
            _arcToolTips.SetToolTip(txtCustomFileName, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Additonal_Information_That_Can_Be_Included_In_The_ISO_File_Name_);
            _arcToolTips.SetToolTip(chkBoxDoNotDownloadVideoFiles, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Select_This_To_Exclude_Downloading_Video_Files_);
            _arcToolTips.SetToolTip(chkBoxDoNotCreateISOImage, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Select_This_To_Bypass_Creating_ISO_Image_);
            _arcToolTips.SetToolTip(chkBoxDoNotUpdateArchiveTables, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Select_This_To_Prevent_Updating_The_System_Database_);
            _arcToolTips.SetToolTip(chkBoxDoNotDeleteDownloadedFiles, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Select_This_To_Ignore_Deleting_Files_Downloaded_Into_Work_Directory_);
            _arcToolTips.SetToolTip(nudMultiFileDownload, Resources.SRIPArchiveClientForm_ApplyArcToolTips_The_Number_Of_Files_To_Download_Concurrently_);
            _arcToolTips.SetToolTip(nudConnections,Resources.SRIPArchiveClientForm_ApplyArcToolTips_The_Number_Of_Concurrent_Persistent_Connections_To_The_Server_);
            _arcToolTips.SetToolTip(nudNumberOfCPUs, Resources.SRIPArchiveClientForm_ApplyArcToolTips_The_number_of_CPU_On_Local_Computer_);
            //
            // Viewer Page...
            //
            _arcToolTips.SetToolTip(txtISOFile,Resources.SRIPArchiveClientForm_ApplyArcToolTips_Location_Of_ISO_File_To_Be_Rendered_In_Viewer_Below_);
            _arcToolTips.SetToolTip(btnISOFileBrowse, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Select_Location_Of_ISO_File_);
            _arcToolTips.SetToolTip(txtISOFileReaderOutputDir, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Path_To_ISO_Viewer_Output_Work_Directory_);
            _arcToolTips.SetToolTip(btnISOReaderOutputDir, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Select_ISO_Viewer_Output_Work_Directory_);
            _arcToolTips.SetToolTip(btnISOFileLoad, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Load_ISO_Input_File_In_Viewer_);
            _arcToolTips.SetToolTip(btnCreateOutputFile, Resources.SRIPArchiveClientForm_ApplyArcToolTips_Create__Restore_or_Cancel_ISO_content_or_processing_);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private void GetEnvironmentData()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter GetEnvironmentData()...");
            try
            {
                Log.LogWrite(string.Format("CurrentDirectory: {0}", Environment.CurrentDirectory));
                //Log.LogWrite(string.Format("MachineName: {0}", Environment.MachineName));
                Log.LogWrite(string.Format("ProcessorCount: {0}", Environment.ProcessorCount));
                Log.LogWrite(string.Format("Affinity Count: {0}", NumberOfProcessorsAvailable));
                Log.LogWrite(string.Format("UserName: {0}", Environment.UserName));
                Log.LogWrite(string.Format("UserDomainName: {0}", Environment.UserDomainName));
                Log.LogWrite(string.Format("CLR Version: {0}", Environment.Version));
                Log.LogWrite(string.Format("OS Version: {0}", Environment.OSVersion));
                Log.LogWrite(string.Format("Platform: {0}", Environment.OSVersion.Platform));
                Log.LogWrite(string.Format("WorkingSet: {0}", Environment.WorkingSet.ToString("#,#")));


                #region SELECT * FROM Win32_ComputerSystem
                using (var query1 = new ManagementObjectSearcher("SELECT * FROM Win32_ComputerSystem"))
                {
                    foreach (ManagementObject mo in query1.Get())
                    {
                        using (mo)
                        {
                            Log.LogWrite("CS - Number Of Physical Processors : " + mo["NumberOfProcessors"]);
                            Log.LogWrite("CS - Number Of Logical Processors : " + mo["NumberOfLogicalProcessors"]);
                            long totalPhysicalMemory = 0;
                            var totalPhysicalMemoryString = mo["totalphysicalmemory"].ToString();
                            if (!string.IsNullOrEmpty(totalPhysicalMemoryString))
                            {
                                totalPhysicalMemory = long.Parse(totalPhysicalMemoryString);
                            }
                            Log.LogWrite("CS - Total Physical Memory : " + totalPhysicalMemory.ToString("#,#"));
                        }
                    }
                }
                #endregion

                #region SELECT * FROM Win32_processor
                using (var query2 = new ManagementObjectSearcher("SELECT * FROM Win32_processor"))
                {
                    var procList = new List<string>();
                    foreach (ManagementObject mo in query2.Get())
                    {
                        using (mo)
                        {
                            var numberOfCores = "PROC - Number Of Cores : " + mo["NumberOfCores"];
                            var numberOfLogicalProcs = "PROC - Number Of Logical Processors : " +
                                                       mo["NumberOfLogicalProcessors"];
                            if (procList.Contains(numberOfCores).Equals(false)) procList.Add(numberOfCores);
                            if (procList.Contains(numberOfLogicalProcs).Equals(false))
                                procList.Add(numberOfLogicalProcs);
                        }
                    }
                    foreach (var p in procList) Log.LogWrite(p);
                }
                #endregion


                #region SELECT * FROM Win32_OperatingSystem
                using (var query3 = new ManagementObjectSearcher("SELECT * FROM Win32_OperatingSystem"))
                {
                    foreach (ManagementObject mo in query3.Get())
                    {
                        using (mo)
                        {
                            Log.LogWrite("OS - Name : " + mo["name"]);
                            Log.LogWrite("OS - Version : " + mo["version"]);
                            Log.LogWrite("OS - Manufacturer : " + mo["Manufacturer"]);
                            Log.LogWrite("OS - Computer Name : " + mo["csname"]);
                            Log.LogWrite("OS - Windows Directory : " + mo["WindowsDirectory"]);
                        }
                    }
                }
                #endregion

                #region SELECT * FROM Win32_bios
                using (var query4 = new ManagementObjectSearcher("SELECT * FROM Win32_bios"))
                {
                    foreach (ManagementObject mo in query4.Get())
                    {
                        using (mo)
                        {
                            Log.LogWrite("BIOS - Version : " + mo["version"]);
                        }
                    }
                }
                #endregion

                #region SELECT * FROM Win32_timezone
                using (var query5 = new ManagementObjectSearcher("SELECT * FROM Win32_timezone"))
                {
                    foreach (ManagementObject mo in query5.Get())
                    {
                        using (mo)
                        {
                            Log.LogWrite("TIMEZONE - Name : " + mo["caption"]);
                        }
                    }
                }
                #endregion

                #region Wrapup...

                var totalMemory = GC.GetTotalMemory(false);
                Log.LogWrite(string.Format(
                    "Estimated amount of memory currently allocated on the managed heap: {0}",
                    totalMemory.ToString("#,#")));

                #endregion

            }
            catch (Exception ex)
            {
                Log.LogWrite(ErrorMessageString(ex));
            }
            finally
            {
                Log.LogWrite("Exit GetEnvironmentData()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private static int GetAffinitizedProcessorCount()
        {
            // gets the number of affinitized proccesors in the
            // current processor group (up to 64 logical processors)
            Process currentProcess = Process.GetCurrentProcess();
            long affinityMask = (long)currentProcess.ProcessorAffinity;
            if (affinityMask == 0) affinityMask = (long)Math.Pow(Environment.ProcessorCount, 2) - 1;

            const int BITS_IN_BYTE = 8;
            int numberOfBits = IntPtr.Size * BITS_IN_BYTE;

            int counter = 0;

            for (int i = 0; i < numberOfBits; i++)
            {
                if ((affinityMask >> i & 1) == 1) counter++;
            }

            return counter;
        }

        /// <summary>
        /// we are looking in the registry for 
        /// the URL that contains
        /// "http://192.168.37.101/CallRecorder "
        /// </summary>
        /// <param name="content"></param>
        /// <returns></returns>
        private string GetApplicationUrl(string content)
        {
            // save the original value...
            string applicationUrl = content;
            try
            {
                // find the application name in the URL...
                content = FindApplicationNameInURL(content);
                // this will not be relevant for FireFox?
                string regKey = @"Software\Microsoft\Internet Explorer\TypedURLs";
                RegistryKey subKey = Registry.CurrentUser.OpenSubKey(regKey);

                int counter = 1;
                while (true)
                {
                    try
                    {
                        // search in ascending order....
                        string valueName = "url" + counter.ToString();
                        string url = subKey.GetValue(valueName).ToString();
                        if (!string.IsNullOrEmpty(url))
                        {
                            if (url.ToUpper().Contains(content.ToUpper()))
                            {
                                // entry keys are stored in the registry as
                                // url1, url2, url3...urln
                                // therefore our ascending search
                                // insures we use the last matching URL entry
                                applicationUrl = url.Substring(0, url.ToUpper().IndexOf(content.ToUpper()) + content.Length) + '/';
                            }
                        }
                        counter++;
                    }
                    catch { /* no more URL entries found so we can exit here... */ break; }
                }
            }
            catch (Exception ex) { UpdateEventViewer(ex.Message, EventLogEntryType.Warning); }
            return applicationUrl;
        }

        /// <summary>
        /// helper method...
        /// </summary>
        /// <param name="content"></param>
        /// <returns></returns>
        private static string FindApplicationNameInURL(string content)
        {
            var webApplicationName = string.Empty;
            // check for ending slash and remove if found
            webApplicationName = content.EndsWith(@"/") ? content.Remove(content.Length - 1) : content;
            // find application name http://localhost/callrecorder
            webApplicationName = webApplicationName.Substring(webApplicationName.LastIndexOf('/'));
            return webApplicationName;
        }

        ////[ End Phase 0 - Initialization ]//////////////////////////////////////
        #endregion


        #region Phase 1 - Retrieving Data via Web Service...
        //////////////////////////////////////////////////////////////////////////

        #region Web Service Background Worker(s)...

        /// <summary>
        /// performs web service data retrieval on a background thread
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void BgWorkerWebServiceDoWork(object sender, DoWorkEventArgs e)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter BgWorkerWebServiceDoWork()...");
            try
            {
                _autoEventMultiFileDownload.Reset();
                _autoEventMaxMultiFileDownloadExceeded.Reset();
                _autoEventAllSQLDataRetrieved.Reset();
                _autoEventAllAudioFilesDownloaded.Reset();
                GetSQLData();
                e.Result = "Success";
            }
            catch (ArcDownloadTimeoutException ex)
            {
                _arcDownLoadTimeOutError = true;
                if (!e.Cancel) _bgWorkerWebService.CancelAsync();
                e.Cancel = true;
                e.Result = "File Download Timeout";
                _bgWorkerErrorMsgs = ex.Message; 
            }
            catch (SRIPArchiveClientFormException s)
            {
                _cancellationWebServiceError = true;
                if (!e.Cancel) _bgWorkerWebService.CancelAsync();
                e.Cancel = true;
                e.Result = "Web Service Failure";
                _bgWorkerErrorMsgs = s.Message;
            }
            catch (FileNotFoundException f)
            {
                _filesNotFoundError = true;
                if (!e.Cancel) _bgWorkerWebService.CancelAsync();
                e.Cancel = true;
                e.Result = "1. File Download Failure";
                _bgWorkerErrorMsgs = f.Message;
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                UpdateEventViewer(_msgs, EventLogEntryType.Error);

                if (!e.Cancel) _bgWorkerWebService.CancelAsync();
                e.Cancel = true;
                e.Result = "2. File Download Failure";
                _bgWorkerErrorMsgs = ex.Message;
            }
            finally
            {
                e.Cancel = _bgWorkerWebService.CancellationPending;
                Log.LogWrite("Exit BgWorkerWebServiceDoWork()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void BgWorkerWebServiceProgressChanged(object sender, ProgressChangedEventArgs e)
        {
            try
            {
                var opi = e.UserState as ObjProgressInfo;

                // first comment...
                if (_showStartUpMsg)
                {
                    PopulateStatusTextBox(string.Format(RES.Resources.RES_AuthenticatedSuccessfullyFoundData
                        , _initialCountOfCallsToDownLoad //CallsArray.Length.ToString()
                        , _maxNumberOfFilesToDownloadConcurrently), true);

                    PopulateStatusTextBox(string.Format(RES.Resources.RES_AuthenticatedSuccessfullyFoundDataPartTwo
                        , !_doNotCreateISOImage
                        , !_doNotUpdateArchiveDbTables
                        , _doNotDeleteDownloadedFiles
                        , NumberOfCPUs
                        , NumberOfCPUConnections
                        , NumberOfCPUs * NumberOfCPUConnections
                        , RequestedConnectionLimit
                        //, ObjFileImageInfo.StartDateRange
                        //, ObjFileImageInfo.EndDateRange)
                        , SetDate(dtpStartDate, dtpStartTime) // don't show user converted time - its confusing...
                        , SetDate(dtpEndDate, dtpEndTime)) // don't show user converted time - its confusing...
                        , true);

                    _showStartUpMsg = false;
                }

                int pos = (int)((double)e.ProgressPercentage / double.Parse(opi._recCount.ToString()) * 100);
                toolStripProgressBar.Value = pos * 2;

                toolStripStatusLabel.Text = string.Format(RES.Resources.RES_FileCountFilesRemainingPctCompletedTimeRemaining
                    , opi._recCount
                    , opi._filesRemaining
                    , (toolStripProgressBar.Value / 2).ToString()
                    //
                    // async downloading may cause us to send the report before the file has
                    // been created...
                    //
                    //" - Size: " + opi._fileSize +
                    , TimeRemainingEstimate(_totalTasksToProcess, (Interlocked.Increment(ref _totalTasksProcessed))));

                // last comment...
                if (opi._completed)
                {
                    PopulateStatusTextBox(
                        // index file *shouldn't* be in the array 
                        // due to async download changes...
                        string.Format(RES.Resources.RES_DownloadedXNumberOfFilesForArchive
                            , (ObjFileImageInfo.PathsAndFileNames.Count).ToString()
                            , ObjFileImageInfo.ArchiveFileName
                            , FormatElapsedTime(_timeRemainingEstimates)), true);
                }
            }
            catch { /*do nothing...*/ }
        }

        /// <summary>
        /// respond to data retrieval completion
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void BgWorkerWebServiceRunWorkerCompleted(object sender, RunWorkerCompletedEventArgs e)
        {
            // wait for data to be downloaded...
            Log.LogWrite("1. ENDING-PHASE-1 BgWorkerWebServiceDoWork(): _autoEventAllSQLDataRetrieved.WaitOne - hold XXXXXXXXXX");
            _autoEventAllSQLDataRetrieved.WaitOne();
            Log.LogWrite("2. END-PHASE-1 BgWorkerWebServiceDoWork(): _autoEventAllSQLDataRetrieved.WaitOne - released XXXXXXXXXX");

            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter BgWorkerWebServiceRunWorkerCompleted()...");
            try
            {

                if (_filesNotFoundError)
                {
                    PopulateStatusTextBox(_filesNotFoundError
                                              ? string.Format(RES.Resources.RES_UnableToDownloadFilesDueTo,
                                                  _bgWorkerErrorMsgs)
                                              : RES.Resources.RES_DataRetrievalCanceled, true);
                    RestoreUI();
                    return;
                }

                if (_arcDownLoadTimeOutError)
                {
                    PopulateStatusTextBox(_arcDownLoadTimeOutError
                                              ? string.Format(Resources.SRIPArchiveClientForm_BgWorkerWebServiceRunWorkerCompleted_File_download_timed_out_,
                                                  _bgWorkerErrorMsgs)
                                              : RES.Resources.RES_DataRetrievalCanceled, true);
                    RestoreUI();
                    return;
                }

                if (e.Cancelled || _cancellationWebServiceError)
                {
                    PopulateStatusTextBox(_cancellationWebServiceError
                                              ? string.Format(RES.Resources.RES_ErrorP1SeeEventViewerForDetails,
                                                  _bgWorkerErrorMsgs)
                                              : RES.Resources.RES_DataRetrievalCanceled, true);
                    RestoreUI();
                    return;
                }

                //
                // jump to the actual image creation
                if (_doNotCreateISOImage.Equals(false))
                {
                    InitCreateISOImage();
                }
                else
                {
                    _autoEventFixZeroByteFileDownloadNoISO.Reset();

                    var zeroByteFileHandlerObject =
                        new ZeroByteFileHandlerForNoISOImageObject
                        {
                            _FileCount = ObjFileImageInfo.PathsAndFileNames.Count
                            ,
                            _ObjFileImageInfo = ObjFileImageInfo
                        };

                    ThreadPool.QueueUserWorkItem(VerifyFilesDownloadedForNoISOImage, zeroByteFileHandlerObject);
                    _autoEventFixZeroByteFileDownloadNoISO.WaitOne();

                    PopulateStatusTextBox(string.Format(RES.Resources.RES_DownloadedXNumberOfFilesForArchive
                        , zeroByteFileHandlerObject._FileCount.ToString()
                        //FixZeroByteFilesForNoISOImage().ToString() // (ObjFileImageInfo.PathsAndFileNames.Count).ToString()
                        , RES.Resources.RES_DownloadedArchiveFilesONLY
                        , FormatElapsedTime(_timeRemainingEstimates)), true);

                    RestoreUI();
                    UpdateConfigSettings();
                }
            }
            finally
            {
                Log.LogWrite("Exit BgWorkerWebServiceRunWorkerCompleted()... " + FormatElapsedTime(stopwatch));
            }
        }

        #region BgWorkerWebService Calls When Completed...

        /// <summary>
        /// run this after successfully gathering
        /// data from SQL database via web service
        /// </summary>
        private void InitCreateISOImage()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            try
            {
                Log.LogWrite("Enter InitCreateISOImage()...");

                if (_cancellationWebServiceError)
                {
                    _msgs = string.Format(RES.Resources.RES_AttemptingToCreateAnISOAfterTheCallToTheWebServiceFailed);
                    PopulateStatusTextBox(_msgs, true);
                    UpdateEventViewer(_msgs, EventLogEntryType.Error);
                    throw new SRIPArchiveClientFormException(RES.Resources.RES_AttemptingToCreateAnISOAfterTheCallToTheWebServiceFailed);
                }

                if (ObjFileImageInfo.PathsAndFileNames.Count > 0)
                {
                    var resetOutputDiskMinimumSize = ResetOutputDiskMinimumSize();

                    if (resetOutputDiskMinimumSize) { }

                    int theLost = CompareDownloadListToISOList();
                    if (theLost > 0)
                    {
                        _msgs = string.Format(RES.Resources.RES_DownloadedLessFileThanExpectedMayNeedToRetryThisBuild
                            , theLost);

                        PopulateStatusTextBox(_msgs, true);

                        foreach (string s in _transportErrors)
                        {
                            // real errors...
                            if (string.IsNullOrEmpty(s)) continue;
                            _msgs = string.Format("File: " + s + " encountered error during download.");
                            PopulateStatusTextBox(_msgs, true);
                        }
                    }

                    FilesToImageRepositoryProcessor();
                }
                else
                {
                    if (!_filesNotFoundError)
                    {
                        _msgs = string.Format(RES.Resources.RES_NoCallsWereFoundThatMatchSearchCriteria);
                        PopulateStatusTextBox(_msgs, true);
                    }
                    RestoreUI();
                }
            }
            finally
            {
                Log.LogWrite("Exit InitCreateISOImage()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// Starts the IsoImageRepository 
        /// creation background worker...
        /// </summary>
        private void FilesToImageRepositoryProcessor()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter FilesToImageRepositoryProcessor()... " + FormatElapsedTime(stopwatch));
            try
            {
                btnCreateOutputFile.Enabled = true;
                _bgWorkerAddFilesToImageRepository.WorkerReportsProgress = true;
                _bgWorkerAddFilesToImageRepository.WorkerSupportsCancellation = true;

                _elapsedIsoCreationTime.Start();
                _msgs = string.Format(RES.Resources.RES_ParsingFilesPleaseWait);
                PopulateStatusTextBox(_msgs, true);

                //_autoEventCreateIsoImageRepository.Reset();

                _bgWorkerAddFilesToImageRepository.DoWork += BgWorkerAddFilesToImageRepositoryDoWork;
                _bgWorkerAddFilesToImageRepository.RunWorkerCompleted += BgWorkerAddFilesToImageRepositoryRunWorkerCompleted;
                _bgWorkerAddFilesToImageRepository.ProgressChanged += BgWorkerAddFilesToImageRepositoryProgressChanged;

                _bgWorkerAddFilesToImageRepository.RunWorkerAsync();

            }
            finally
            {
                Log.LogWrite("Exit FilesToImageRepositoryProcessor()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// See if any one file is 
        /// greater than the selected
        /// output media size; if yes
        /// increase the media size
        /// </summary>
        private bool ResetOutputDiskMinimumSize()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter ResetOutputDiskMinimumSize()...");
            bool oversizedFile = false;

            try
            {
                Log.LogWrite(string.Format("Before output media size: {0}", _formatFileSize.ToString("#,#")));
                var largestFileSizeInList = ObjFileImageInfo.PathsAndFileNames.Max(item => new FileInfo(item).Length);
                Log.LogWrite("Largest file in list: " + largestFileSizeInList.ToString("#,#"));

                if (largestFileSizeInList >= _formatFileSize && _formatFileSize == _maxCDFormatFileSize)
                {
                    oversizedFile =
                        radioBtnDVD.Checked = true;
                }

                if (largestFileSizeInList >= _formatFileSize && _formatFileSize == _maxDVDFormatFileSize)
                {
                    oversizedFile =
                        radioBtnOther.Checked = true;
                }

                if (largestFileSizeInList >= _udfRequiredSingleFileSize)
                {
                    oversizedFile =
                        _udfFileSystemRequired =
                        radioBtnOther.Checked = true;
                    Log.LogWrite(string.Format("Oversized file size found is greater than: {0} --- set file image type to UDF"
                        , _udfRequiredSingleFileSize.ToString("#,#")));
                }

                if (largestFileSizeInList >= _formatFileSize && _formatFileSize == _maxUDFFormatFileSize)
                {
                    oversizedFile = true;
                    Log.LogWrite(string.Format("Largest file size found is greater than: {0}", _maxUDFFormatFileSize.ToString("#,#")));
                }
            }
            finally
            {
                Log.LogWrite(string.Format("After output media size: {0}", _formatFileSize.ToString("#,#")));
                Log.LogWrite("Exit ResetOutputDiskMinimumSize()... " + FormatElapsedTime(stopwatch));
            }

            return oversizedFile;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="zeroByteFileHandlerObject"></param>
        private void VerifyFilesDownloadedForNoISOImage(object zeroByteFileHandlerObject)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter VerifyFilesDownloadedForNoISOImage()...");

            var obj = zeroByteFileHandlerObject as ZeroByteFileHandlerForNoISOImageObject;
            try
            {
                if (null != obj)
                {
                    var isoDirectoryLayout = new FileInfo(txtISODirectoryLayout.Text).DirectoryName;
                    var dirInfo = new DirectoryInfo(isoDirectoryLayout);

                    foreach (FileInfo fi in dirInfo.GetFiles().Where(n => n.Length < 1 && obj._ObjFileImageInfo.PathsAndFileNames.Contains(n.FullName)))
                    {
                        if (null == fi) continue;
                        string path = fi.FullName;
                        if (string.IsNullOrEmpty(path)) continue;
                        if (path.Contains(RES.Resources.RES_IndexCSVFileName)) continue;

                        FileImageInfo.IndexData fii = (obj._ObjFileImageInfo.IndexFileData.Find(i => i.RecordedFileName.Equals(path)));
                        if (null != fii)
                        {
                            if (fii.Duration > 0)
                            {
                                try
                                {
                                    if (!PopulateStatusTextBox(string.Format(RES.Resources.RES_ZeroByteFileFound, path, fii.Duration), true))
                                        SaveTransportErrors(string.Format(RES.Resources.RES_ZeroByteFileFound, path, fii.Duration));
                                }
                                catch { }
                                RecordedCalls rc = CallsArray.First(n => n.CallID.Equals(fii.CallID));
                                if (null != rc)
                                {
                                    string downLoadPath = _isoDirectoryLayout + (new FileInfo(rc.RecordingFileLocation).Name);
                                    using (var awc = new ArchiveWebClient(300000)) // wait 5 minutes...
                                    {
                                        awc.UseDefaultCredentials = true;
                                        try
                                        {
                                            awc.DownloadFile(new Uri(rc.RecordingFileLink), downLoadPath);
                                            Log.LogWrite(string.Format("Successfully downloaded {0} - bytes: {1}", path, new FileInfo(path).Length));
                                        }
                                        catch (Exception se)
                                        {
                                            _msgs = string.Format(RES.Resources.RES_VerifyZeroByteFileDownloadError,
                                                downLoadPath
                                                , obj._FileCount
                                                , obj._FileCount - 1
                                                , ErrorMessageString(se));

                                            if (!PopulateStatusTextBox(string.Format(_msgs), true))
                                                UpdateEventViewer(_msgs, EventLogEntryType.Error);

                                            // subtract from total...
                                            obj._FileCount -= 1;
                                        }
                                    }
                                }
                            }
                            else
                            {
                                Log.LogWrite(string.Format("Recording duration is 0 - valid zero-byte file: {0}", path));
                            }
                        }
                    }
                }
            }
            catch (Exception se)
            {
                _msgs = ErrorMessageString(se);
                if (!PopulateStatusTextBox(string.Format(_msgs), true))
                    UpdateEventViewer(_msgs, EventLogEntryType.Error);
            }
            finally
            {
                Log.LogWrite("Exit VerifyFilesDownloadedForNoISOImage()... " + FormatElapsedTime(stopwatch));
                _autoEventFixZeroByteFileDownloadNoISO.Set();
            }
        }

        #endregion

        #endregion

        #region Web Service Data Retrieval Support...
        ////////////////////////////////////////////////////////////////////////// 

        /// <summary>
        /// ask the web service for
        /// some call records and videos 
        /// stored in the main SQL database...
        /// </summary>
        private void GetSQLData()
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter GetSQLData()...");
            var eTime = DateTime.Now.ToString();

            try
            {
                #region Initialize...

                lock (_objectLock)
                {
                    ObjFileImageInfo = null;
                    ObjFileImageInfo = new FileImageInfo();
                    ObjFileImageInfo.Initialize();
                }

                // set the start time to 00:00:00 of the start day           
                ObjFileImageInfo.StartDateRange =
                    Convert.ToDateTime(
                        TimeZoneData.ConvertTimeZoneToUtc(
                            SetDate(dtpStartDate, dtpStartTime), _currentTimeZoneSelected).ToString());

                // set the end time to 23:59:59 of the end day
                ObjFileImageInfo.EndDateRange =
                    Convert.ToDateTime(
                        TimeZoneData.ConvertTimeZoneToUtc(
                            SetDate(dtpEndDate, dtpEndTime), _currentTimeZoneSelected).ToString());

                ObjFileImageInfo.VolumeName = _mediaVolumeName;
                ObjFileImageInfo.ArchiveFileName = _outputLocation;
                ObjFileImageInfo.UserName = _userName;
                ObjFileImageInfo.PassWord = _password;

                // get web service URL...
                var classicArchiveWS = ClassicArchiveWS;
                Log.LogWrite("URL: " + classicArchiveWS.Url);

                var attempts = 0;
                var done = false;
                var audioDuplicates = 0;
                var videoDuplicates = 0;
                //
                // reset member accums...
                _videosToDownLoadCount =
                    _countOfAudioWithNoRecordingFileLocation =
                    _countOfScreenRecordingWithNoRecordingFileLocation = 0;

                #endregion

                #region get recorded call (MP3) data from server...

                /////////////////////////////////////////////////////////////////////
                PopulateCallsArrayObject(ref attempts, ref done, classicArchiveWS);
                if (null != CallsArray)
                {
                    Log.LogWrite(string.Format("CallsArray count: {0}", CallsArray.Length));
                    var counter = 0;
                    foreach (RecordedCalls s in CallsArray.ToList())
                    {
                        if (_cancellationPendingWebService)
                        {
                            Log.LogWrite(string.Format("Canceled web service request for data..."));
                            return;
                        }

                        if (string.IsNullOrEmpty(s.RecordingFileLocation))
                        {
                            Interlocked.Increment(ref _countOfAudioWithNoRecordingFileLocation);
                            Log.LogWrite(string.Format("Audio: RecordingFileLocation ({1}) not found for {0}",
                                s.CallID,
                                s.RecordingFileLink));
                            continue;
                        }

                        Log.LogWrite(string.Format("[Rec: {0}] {1}", Interlocked.Increment(ref counter),
                            s.RecordingFileLocation.Substring(
                                s.RecordingFileLocation.LastIndexOf("\\",
                                    StringComparison.Ordinal) + 1)));
                    }
                    audioDuplicates = ProcessAudioDuplicates(audioDuplicates);
                    RemoveAllRecordsWithNoRecordingFileLocation();
                }
                else Log.LogWrite("CallsArray object is null...");
                /////////////////////////////////////////////////////////////////////

                #endregion

                #region get screen recording video (SRF) data from server...

                /////////////////////////////////////////////////////////////////////
                if (_doNotDownloadVideoFiles.Equals(false))
                {
                    attempts = 0;
                    done = false;
                    PopulateScreenRecordingVideoArrayObject(ref attempts, ref done, classicArchiveWS);
                    if (null != ScreenRecordingVideoArray)
                    {
                        Log.LogWrite(string.Format("Expected ScreenRecordingVideoArray Count: {0}",
                            ScreenRecordingVideoArray.Length));
                        int counter = 0;
                        foreach (ScreenRecordingForArchival s in ScreenRecordingVideoArray.ToList())
                        {

                            if (_cancellationPendingWebService)
                            {
                                Log.LogWrite(string.Format("Canceled web service request for data..."));
                                return;
                            }

                            if (s.RecordingFileLocation == null)
                            {
                                Interlocked.Increment(ref _countOfScreenRecordingWithNoRecordingFileLocation);
                                Log.LogWrite(string.Format("Video: RecordingFileLocation not found for {0}",
                                    s.CallId));
                                continue;
                            }

                            Log.LogWrite(string.Format("[Rec: {0}, CallID: {2}] {1}"
                                , Interlocked.Increment(ref counter)
                                ,
                                s.RecordingFileLocation.Substring(
                                    s.RecordingFileLocation.LastIndexOf("\\",
                                        StringComparison.Ordinal) +
                                    1)
                                , s.CallId));
                        }

                        videoDuplicates = ProcessVideoDuplicates(videoDuplicates);
                        RemoveAllVideosWithNoRecordingFileLocation();
                        Log.LogWrite(string.Format("Actual ScreenRecordingVideoArray Count: {0}",
                            ScreenRecordingVideoArray.Length));
                    }
                    else Log.LogWrite("ScreenRecordingVideoArray object is null...");
                }
                else
                {
                    Log.LogWrite("Do not download video files with this run...");
                }
                ///////////////////////////////////////////////////////////////////////

                #endregion

                #region Notes...

                ///////////////////////////////////////////////////////////////////////
                /* 
                     * Now that we have our list of MP3's and SRF's,
                     * the next thing to do is download the SRF files.
                     * 
                     * However, currently we download MP3 files only.
                     * So that means that *everything* from this point  
                     * was customized to perform this singular task. 
                     * 
                     * This includes performing the following:
                     * 
                     *      1. Download multiple MP3 files
                     *      2. Asynchronously track the download and update 
                     *      the applicable properties with the results                                  
                     *      3. Add the location of each of the MP3 files to
                     *      the ISO Image Repository object
                     *      4. Build in access to any downloaded MP3 via
                     *      the ISO Image Viewer and the local media player
                     *      5. Restore MP3 and associated data to database on demand.
                     *      
                     * So, what do we need to do to download/restore/play an SRF file?     
                     * 
                     * First, we need to modify the current process to download more
                     * than just one file type. This will modifying the download process
                     * to have a stageing area for launching download requests. This will
                     * make it easier to add some other file type in the future. We will
                     * apply this change in the DownLoadRecordedMediaProcessor().
                     * 
                     * Restore and playback are TBD...
                    */
                ///////////////////////////////////////////////////////////////////////

                #endregion

                #region Ready...

                if (CallsArray != null)
                {
                    Log.LogWrite("Total audio duplicates: " + audioDuplicates);
                    Log.LogWrite("Total audio with no recording file location: " +
                                 _countOfAudioWithNoRecordingFileLocation);
                    Log.LogWrite("Total video duplicates: " + videoDuplicates);
                    Log.LogWrite("Total video with no recording file location: " +
                                 _countOfScreenRecordingWithNoRecordingFileLocation);

                    var totalRecordsMatchingSearchCriteria = CallsArray.Length;

                    if (totalRecordsMatchingSearchCriteria > 0)
                    {
                        var totalWeDownloadedSuccessfully = 0;
                        _showStartUpMsg = true; // global support for multi file stuff

                        // add screen recordings to the big count now...
                        if (_doNotDownloadVideoFiles.Equals(false) && null != ScreenRecordingVideoArray)
                        {
                            _totalNumberOfVideoFilesToDownload = ScreenRecordingVideoArray.Length;
                            _videosToDownLoadCount = _totalNumberOfVideoFilesToDownload;
                            totalRecordsMatchingSearchCriteria += _totalNumberOfVideoFilesToDownload;
                        }

                        _callsToDownLoadCount = totalRecordsMatchingSearchCriteria;
                        // global to support multi file downloads...
                        _initialCountOfCallsToDownLoad = _callsToDownLoadCount;

                        Log.LogWrite(string.Format("Total Calls to Download: {0}", _callsToDownLoadCount));

                        // now we know how many recs we can expect            
                        _totalTasksToProcess = totalRecordsMatchingSearchCriteria + 1; // add the index.csv file
                        // reset the recs processed tracker
                        _totalTasksProcessed = 0;

                        #region helper objects...

                        //////////////////////////////////////////////////////////////////////////        

                        List<ScreenRecordingForArchival> listSRFA;
                        listSRFA = null != ScreenRecordingVideoArray
                                       ? new List<ScreenRecordingForArchival>(ScreenRecordingVideoArray)
                                       : new List<ScreenRecordingForArchival>();

                        //////////////////////////////////////////////////////////////////////////        

                        #endregion

                        // start tracking download elapsed time...
                        _elapsedFileDownloadTime.Reset();
                        _elapsedFileDownloadTime.Start();

                        // download the call records asynchronously... 
                        totalWeDownloadedSuccessfully =
                            DownLoadRecordedMediaProcessor(totalRecordsMatchingSearchCriteria
                                , totalWeDownloadedSuccessfully
                                , CallsArray
                                , ObjFileImageInfo
                                , listSRFA);

                        // support async downloads by waiting here until done...
                        WaitForDownloadsToComplete();

                        // throw new Exception(@"Test multi threaded error handling...");

                        // grab elapsed time now...
                        eTime = FormatElapsedTime(_elapsedFileDownloadTime);

                        // now get back to work!
                        Application.DoEvents();

                        // this is the number of files we downloaded
                        ObjFileImageInfo.ItemCount = totalWeDownloadedSuccessfully;

                        //
                        // since we have gotten the files we need 
                        // from the main DB, we will ask the ISO
                        // writer to ignore these dates...
                        //
                        ObjFileImageInfo.UseObjectDates = false;
                    }
                }
                else Log.LogWrite("CallsArray object is null...");

                #endregion
            }
            catch(ArcDownloadTimeoutException)
            {
                throw;
            }
            catch (Exception ex)
            {
                Log.LogWrite(ErrorMessageString(ex));
                throw; // make sure the error makes it back to the caller
            }
            finally
            {
                Log.LogWrite("Get totals before exiting GetSQLData()... ");
                try
                {
                    const string results = "[TOTAL BYTES DOWNLOADED: {0} ({1})] ==== [TOTAL ELAPSED DOWNLOAD TIME: {2}]";
                    long bytes = 0;
                    if (ObjFileImageInfo != null && ObjFileImageInfo.PathsAndFileNames != null)
                    {
                        foreach (var s in ObjFileImageInfo.PathsAndFileNames.Where(s => !string.IsNullOrEmpty(s)))
                        {
                            try
                            {
                                bytes += new FileInfo(s).Length;
                            }
                            catch { /* do nothing here...*/ }
                        }
                    }
                    var convertedByteDescritpion = ConvertBytesToString(bytes);
                    Log.LogWrite(string.Format(results, bytes.ToString("#,#"), convertedByteDescritpion, eTime));
                }
                finally
                {
                    // done over here...
                    Log.LogWrite("Exit GetSQLData()... " + FormatElapsedTime(stopwatch));
                    _autoEventAllSQLDataRetrieved.Set();
                }
            }
        }

        /// <summary>
        /// iterate over the audio and video
        /// lists and pull each recording
        /// down to the client pc... 
        /// </summary>
        /// <param name="totalRecordsMatchingSearchCriteria"></param>
        /// <param name="totalWeDownloadedSuccessfully"></param>
        /// <param name="callsArray"></param>
        /// <param name="objFileImageInfo"></param>
        /// <param name="listSRFA"></param>
        /// <returns></returns>
        private int DownLoadRecordedMediaProcessor(int totalRecordsMatchingSearchCriteria
                                                   , int totalWeDownloadedSuccessfully
                                                   , RecordedCalls[] callsArray
                                                   , FileImageInfo objFileImageInfo
                                                   , List<ScreenRecordingForArchival> listSRFA)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            try
            {
                Log.LogWrite("Enter DownLoadRecordedMediaProcessor()...");
                lock (_downloadPadLock)
                {
                    _currentDownloadFileCount = 0;
                    _saveMaxNumberOfFilesToDownloadConcurrently = _maxNumberOfFilesToDownloadConcurrently;
                    _saveNumberOfCPUs = _numberOfCPUs;
                }
                var listCallsWithVideos = new List<RecordedCalls>();

                if (callsArray.Length > 0)
                {
                    totalWeDownloadedSuccessfully = MP3DownLoadProcessor(totalRecordsMatchingSearchCriteria
                        , callsArray
                        , objFileImageInfo
                        , listSRFA
                        , listCallsWithVideos);
                }

                if (_doNotDownloadVideoFiles.Equals(true)) { lock (_downloadPadLock) { _totalNumberOfVideoFilesToDownload = 0; } }

                Log.LogWrite("1. *#*#*#*#*# DownLoadRecordedMediaProcessor(): _autoEventAllAudioFilesDownloaded.WaitOne - hold for max of 5 minutes *#*#*#*#*#");
                var mainMediaDownLoadTimedOut = !_autoEventAllAudioFilesDownloaded.WaitOne(TimeSpan.FromMinutes(5));
                Log.LogWrite(string.Format("2. *#*#*#*#*# DownLoadRecordedMediaProcessor(): _autoEventAllAudioFilesDownloaded.WaitOne - release {0} *#*#*#*#*#", (mainMediaDownLoadTimedOut ? "execeed time limit" : "succeeded")));

                if (mainMediaDownLoadTimedOut)
                {
                    // force clean up...
                    WcDownloadFileCompleted(new ArchiveWebClient(), null);
                    Log.LogWrite("3. *#*#*#*#*# DownLoadRecordedMediaProcessor(): _autoEventAllAudioFilesDownloaded.WaitOne - hold for max of 5 minutes *#*#*#*#*#");
                    mainMediaDownLoadTimedOut = !_autoEventAllAudioFilesDownloaded.WaitOne(TimeSpan.FromMinutes(5));
                    Log.LogWrite(string.Format("4. *#*#*#*#*# DownLoadRecordedMediaProcessor(): _autoEventAllAudioFilesDownloaded.WaitOne - release {0} *#*#*#*#*#", (mainMediaDownLoadTimedOut ? "execeed time limit" : "succeeded")));
                    throw new ArcDownloadTimeoutException("ARC file download (main media) timed out; ending session.");
                }

                if (_totalNumberOfVideoFilesToDownload > 0)
                {
                    Log.LogWrite("Before _maxNumberOfFilesToDownloadConcurrently: " + _maxNumberOfFilesToDownloadConcurrently);
                    Log.LogWrite("Before _numberOfCPUs: " + _numberOfCPUs);
                    lock (_downloadPadLock)
                    {
                        // 
                        // SRF files are not downloading consistently
                        // when the concurrent file setting is > 1;
                        // Experienced this problem with x64
                        _maxNumberOfFilesToDownloadConcurrently = 1;

                        // SRF files are not downloading consistently
                        // when the number of CPU's is > 1;
                        // Experienced this problem with x64
                        _numberOfCPUs = 1;
                    }

                    Log.LogWrite("After _maxNumberOfFilesToDownloadConcurrently: " + _maxNumberOfFilesToDownloadConcurrently);
                    Log.LogWrite("After _numberOfCPUs: " + _numberOfCPUs);

                    var tempListCallsWithVideos = new List<RecordedCalls>(listCallsWithVideos);
                    var tempTotalWeDownloadedSuccessfully = totalWeDownloadedSuccessfully;
                    totalWeDownloadedSuccessfully = VideoDownLoadProcessor(totalRecordsMatchingSearchCriteria
                        , tempTotalWeDownloadedSuccessfully
                        , objFileImageInfo
                        , listSRFA
                        , tempListCallsWithVideos);
                }

            }
            catch (ArcDownloadTimeoutException)
            {
                throw;
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                Log.LogError("Error in DownLoadRecordedMediaProcessor(): " + _msgs);
            }
            finally
            {
                lock (_downloadPadLock)
                {
                    _maxNumberOfFilesToDownloadConcurrently = _saveMaxNumberOfFilesToDownloadConcurrently;
                    _numberOfCPUs = _saveNumberOfCPUs;
                }
                Log.LogWrite("Total downloaded successfully: " + totalWeDownloadedSuccessfully);
                Log.LogWrite("Exit DownLoadRecordedMediaProcessor()... " + FormatElapsedTime(stopwatch));
            }
            return totalWeDownloadedSuccessfully;
        }

        /// <summary>
        /// this is always performed...
        /// </summary>
        /// <param name="totalRecordsMatchingSearchCriteria"></param>
        /// <param name="callsArray"></param>
        /// <param name="objFileImageInfo"></param>
        /// <param name="listSRFA"></param>
        /// <param name="listCallsWithVideos"></param>
        /// <returns></returns>
        private int MP3DownLoadProcessor(int totalRecordsMatchingSearchCriteria
                                         , RecordedCalls[] callsArray
                                         , FileImageInfo objFileImageInfo
                                         , List<ScreenRecordingForArchival> listSRFA
                                         , List<RecordedCalls> listCallsWithVideos)
        {
            var totalWeDownloadedSuccessfully = 0;
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter MP3DownLoadProcessor()...");
            try
            {
                foreach (RecordedCalls rc in callsArray)
                {
                    if (null == rc) continue;

                    if (_cancellationPendingWebService)
                    {
                        // check to see if the cancel button
                        // was clicked before we downloaded any
                        // files...
                        if (1 > totalWeDownloadedSuccessfully)
                        {
                            // since no files have been downloaded
                            // we will manually call the method that
                            // handles releasing the thread sync objects
                            //WcDownloadFileCompleted(null, null);
                            WcDownloadFileCompleted(new ArchiveWebClient(), null); 
                        }
                        return 0; // return a count of zero calls downloaded...
                    }

                    #region Comments...
                    ////////////////////////////////////////////////////
                    /*
                     * As part of the modification to download multiple
                     * file types (MP3,SRF,etc), we will refactor the code 
                     * previously found here and replicate it for each file 
                     * type downloaded. The foundation for this approach 
                     * is that each RC will contain information
                     * about the new file type; for now that means this
                     * call record has an audio file and a video file. 
                     * So we will loop over the calls and, while downloading
                     * the audio, we will also download the video that
                     * belongs to this call as well. Later, in the ISO
                     * Builder stage, we will look for the audio and video
                     * files that belongs to the call and place each item
                     * on the ISO...
                     */
                    ////////////////////////////////////////////////////
                    #endregion

                    // check before downloading...
                    if ((_currentDownloadFileCount > _maxNumberOfFilesToDownloadConcurrently))
                    {
                        Log.LogWrite("1.*********** MP3DownLoadProcessor(): _autoEventMaxMultiFileDownloadExceeded.WaitOne - hold ***********");

                        var downloadTimedOut = !_autoEventMaxMultiFileDownloadExceeded.WaitOne(TimeSpan.FromSeconds(90));
                        if (downloadTimedOut)
                        {
                            Log.LogWrite("1a.*********** MP3DownLoadProcessor(): _autoEventMaxMultiFileDownloadExceeded.WaitOne - download time exceeded, end session... ***********");
                            WcDownloadFileCompleted(new ArchiveWebClient(), null);
                            throw new ArcDownloadTimeoutException("ARC file download (audio) timed out; ending session.");
                        }

                        Log.LogWrite("2.*********** MP3DownLoadProcessor(): _autoEventMaxMultiFileDownloadExceeded.WaitOne - released ***********");
                    }
                    //
                    // load list of calls with videos...
                    ScreenRecordingForArchival srfa = GetVideoByCallId(listSRFA, rc.CallID);
                    if (null != srfa)
                    {
                        if (!string.IsNullOrEmpty(srfa.RecordingFileLocation)) listCallsWithVideos.Add(rc);
                    }
                    //
                    // download the audio recording now
                    DownloadMP3File(totalRecordsMatchingSearchCriteria
                        , ref totalWeDownloadedSuccessfully
                        , objFileImageInfo
                        , srfa
                        , rc);

                    Log.LogWrite("$$$$$$$$$ Running download total: " + totalWeDownloadedSuccessfully);
                }
                return totalWeDownloadedSuccessfully;
            }
            finally
            {
                //_autoEventAllAudioFilesDownloaded.Set();
                Log.LogWrite("Exit MP3DownLoadProcessor()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="totalRecordsMatchingSearchCriteria"></param>
        /// <param name="totalWeDownloadedSuccessfully"></param>
        /// <param name="objFileImageInfo"></param>
        /// <param name="localSRFA"> </param>
        /// <param name="rc"></param>
        private void DownloadMP3File(int totalRecordsMatchingSearchCriteria
                                     , ref int totalWeDownloadedSuccessfully
                                     , FileImageInfo objFileImageInfo
                                     , ScreenRecordingForArchival localSRFA
                                     , RecordedCalls rc)
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter DownloadMP3File()...");
            try
            {
                #region Download multiple MP3 files...

                //////////////////////////////////////////////////////////////////////////

                // this is the location of the temp folder
                // where we will place the file streamed to
                // us by the link provider.                
                var mp3DownLoadPath = _isoDirectoryLayout + (new FileInfo(rc.RecordingFileLocation).Name);
                Log.LogWrite("DownloadMP3File() processing: " + mp3DownLoadPath);

                //
                // Future?
                //
                // switch to bitsLink for URI download...
                //Log.LogWrite("RecordingFileLink before: " + rc.RecordingFileLink);
                //string recordingFileLinkForBitsLink = rc.RecordingFileLink
                //    .Replace("LinkProvider", "BitsLink")
                //    .Replace("rcd=", "eid=")
                //    .Replace("TildeCode", "~");
                //Log.LogWrite("RecordingFileLink after: " + recordingFileLinkForBitsLink);
                //

                var recordingFileLinkForBitsLink = rc.RecordingFileLink;

                if (string.IsNullOrEmpty(rc.RecordingFileLink))
                {
                    {
                        lock (_downloadPadLock)
                        {
                            _msgs =
                                string.Format(
                                    "RecordingFileLink property not found for \"{0}\"; this issue suggests that there is a version mismatch between the web service request and the SmartRecord endpoint...",
                                    mp3DownLoadPath);
                            Log.LogWrite(_msgs);
                            // force clean up...
                            //WcDownloadFileCompleted(null, null);
                            WcDownloadFileCompleted(new ArchiveWebClient(), null); 
                        }
                    }
                }
                else
                {

                    #region Helpers...

                    //////////////////////////////////////////////////////////////////////////
                    // create new progress object...
                    ObjProgressInfo localObjPI = new ObjProgressInfo
                    {
                        _fileName = mp3DownLoadPath
                        ,
                        _recCount = totalRecordsMatchingSearchCriteria
                        ,
                        _filesRemaining =
                            totalRecordsMatchingSearchCriteria -
                            totalWeDownloadedSuccessfully
                        ,
                        _startup = _showStartUpMsg
                        ,
                        _completed =
                            (totalRecordsMatchingSearchCriteria -
                             totalWeDownloadedSuccessfully).Equals(0)
                    };

                    // create new download async object 
                    DownLoadFileObject localDlMP3obj = new DownLoadFileObject
                    {
                        _rc = rc
                        ,
                        _downLoadPath = mp3DownLoadPath
                        ,
                        _recordingLinkURL = recordingFileLinkForBitsLink
                            //rc.RecordingFileLink
                        ,
                        _objPI = localObjPI
                        ,
                        _totalWeDownloadedSuccessfully =
                            totalWeDownloadedSuccessfully
                        ,
                        _bgWorkerWebServiceMP3 = _bgWorkerWebService
                        ,
                        _objFileImageInfo = objFileImageInfo
                        ,
                        _srfa = localSRFA
                    };
                    //////////////////////////////////////////////////////////////////////////

                    #endregion

                    // pass the object to the method that
                    // actually downloads the mp3...
                    lock (_downloadPadLock)
                    {
                        var found = AsyncFileDownLoader(localDlMP3obj);

                        if (found)
                        {
                            Interlocked.Increment(ref _currentDownloadFileCount);
                            Interlocked.Increment(ref totalWeDownloadedSuccessfully);
                        }
                        else
                        {
                            Interlocked.Decrement(ref _callsToDownLoadCount);
                            UpdateEventViewer(string.Format("Record not found: {0} URI: {1}", mp3DownLoadPath,
                                string.IsNullOrEmpty(localDlMP3obj._rc.RecordingFileLink)
                                    ? "No URI provided"
                                    : localDlMP3obj._rc.RecordingFileLink),
                                EventLogEntryType.Error);
                            Log.LogWrite("New callsToDownLoad count: " + _callsToDownLoadCount);
                        }
                    }
                    //////////////////////////////////////////////////////////////////////////        
                }

                #endregion
            }
            finally
            {
                Log.LogWrite("Exit DownloadMP3File()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// this is optional...
        /// </summary>
        /// <param name="totalRecordsMatchingSearchCriteria"></param>
        /// <param name="totalWeDownloadedSuccessfully"></param>
        /// <param name="objFileImageInfo"></param>
        /// <param name="refListSRFA"> </param>
        /// <param name="refListCallsWithVideos"> </param>
        /// <returns></returns>
        private int VideoDownLoadProcessor(int totalRecordsMatchingSearchCriteria
                                         , int totalWeDownloadedSuccessfully
                                         , FileImageInfo objFileImageInfo
                                         , List<ScreenRecordingForArchival> refListSRFA
                                         , List<RecordedCalls> refListCallsWithVideos)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter VideoDownLoadProcessor()...");
            try
            {
                var screenRecordingsForArchival = new List<ScreenRecordingForArchival>(refListSRFA);
                var callsWithVideos = new List<RecordedCalls>(refListCallsWithVideos);

                foreach (var srfa in screenRecordingsForArchival)
                {
                    if (null == srfa)
                    {
                        Log.LogWrite("SRFA object is null - fire null download event...");
                        //WcDownloadFileCompleted(null, null);
                        WcDownloadFileCompleted(new ArchiveWebClient(), null); 
                        continue;
                    }

                    if (_cancellationPendingWebService)
                    {
                        // check to see if the cancel button
                        // was clicked before we downloaded any
                        // files...
                        if (1 > totalWeDownloadedSuccessfully)
                        {
                            // since no files have been downloaded
                            // we will manually call the method that
                            // handles releasing the thread sync objects
                            WcDownloadFileCompleted(new ArchiveWebClient(), null); 
                        }
                        return 0; // return a count of zero calls downloaded...
                    }

                    #region Comments...
                    ////////////////////////////////////////////////////
                    /*
                     * As part of the modification to download multiple
                     * file types (MP3,SRF,etc), we will refactor the code 
                     * previously found here and replicate it for each file 
                     * type downloaded. The foundation for this approach 
                     * is that each RC will contain information
                     * about the new file type; for now that means this
                     * call record has an audio file and a video file. 
                     * So we will loop over the calls and, while downloading
                     * the audio, we will also download the video that
                     * belongs to this call as well. Later, in the ISO
                     * Builder stage, we will look for the audio and video
                     * files that belongs to the call and place each item
                     * on the ISO...
                     */
                    ////////////////////////////////////////////////////
                    #endregion

                    // check before downloading...
                    if ((_currentDownloadFileCount > _maxNumberOfFilesToDownloadConcurrently))
                    {
                        Log.LogWrite(
                            "1.*********** VideoDownLoadProcessor(): _autoEventMaxMultiFileDownloadExceeded.WaitOne - hold ***********");

                        var downloadTimedOut = !_autoEventMaxMultiFileDownloadExceeded.WaitOne(TimeSpan.FromSeconds(90));
                        if (downloadTimedOut)
                        {
                            Log.LogWrite("1a.*********** VideoDownLoadProcessor(): _autoEventMaxMultiFileDownloadExceeded.WaitOne - download time exceeded, end session... ***********");
                            WcDownloadFileCompleted(new ArchiveWebClient(), null);
                            throw new ArcDownloadTimeoutException("ARC file download (video) timed out; ending session.");
                        }

                        Log.LogWrite(
                            "2.*********** VideoDownLoadProcessor(): _autoEventMaxMultiFileDownloadExceeded.WaitOne - released ***********");
                    }

                    // find the owner of the video...
                    RecordedCalls localRC = callsWithVideos.Find(i => i.CallID.Equals(srfa.CallId));
                    //
                    // download the video recording now
                    DownloadVideoFile(totalRecordsMatchingSearchCriteria
                        , ref totalWeDownloadedSuccessfully
                        , objFileImageInfo
                        , srfa
                        , localRC);

                    Log.LogWrite("$$$$$$$$$ Running download total: " + totalWeDownloadedSuccessfully);
                }
                return totalWeDownloadedSuccessfully;
            }
            finally
            {
                Log.LogWrite("Exit VideoDownLoadProcessor()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="totalRecordsMatchingSearchCriteria"></param>
        /// <param name="totalWeDownloadedSuccessfully"></param>
        /// <param name="objFileImageInfo"></param>
        /// <param name="localSRFA"> </param>
        /// <param name="rc"></param>
        private void DownloadVideoFile(int totalRecordsMatchingSearchCriteria
                                     , ref int totalWeDownloadedSuccessfully
                                     , FileImageInfo objFileImageInfo
                                     , ScreenRecordingForArchival localSRFA
                                     , RecordedCalls rc)
        {
            if (_doNotDownloadVideoFiles) return;

            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter DownloadVideoFile()...");
            try
            {
                #region Download video files...
                //////////////////////////////////////////////////////////////////////////                            
                try
                {
                    Log.LogWrite("Evaluate local copy of ScreenRecordingForArchival object...");
                    if (null != localSRFA && (!string.IsNullOrEmpty(localSRFA.RecordingFileLocation) || localSRFA.RecordingGuid.Equals(Guid.Empty)))
                    {
                        Log.LogWrite("Evaluate successful!");
                        //
                        // the location of CallRecorder to                 
                        string videoLinkURL = localSRFA.ScreenRecordingVideoLink.Replace("&SRF=", "&SCR=");
                        string srfDownLoadPath = _isoDirectoryLayout + (new FileInfo(localSRFA.RecordingFileLocation).Name);

                        Log.LogWrite("DownloadVideoFile() processing: " + srfDownLoadPath);

                        try
                        {
                            if (File.Exists(srfDownLoadPath))
                            {
                                Log.LogWrite("File exists - need to delete: " + srfDownLoadPath);
                                var fi = new FileInfo(srfDownLoadPath);
                                fi.Attributes = FileAttributes.Normal;
                                fi.Delete();
                                if (File.Exists(srfDownLoadPath).Equals(false))
                                    Log.LogWrite("File deleted: " + srfDownLoadPath);
                                else
                                    Log.LogWrite("Unable to delete: " + srfDownLoadPath);
                            }
                        }
                        catch (Exception ex)
                        {
                            Log.LogWrite("Error - unable to delete: " + srfDownLoadPath);
                            Log.LogWrite(ErrorMessageString(ex));
                        }

                        #region Helpers...
                        //////////////////////////////////////////////////////////////////////////
                        // create new progress object...
                        var localObjPI = new ObjProgressInfo
                        {
                            _fileName = srfDownLoadPath
                            ,
                            _recCount = totalRecordsMatchingSearchCriteria
                            ,
                            _filesRemaining = totalRecordsMatchingSearchCriteria - totalWeDownloadedSuccessfully
                            ,
                            _startup = _showStartUpMsg
                            ,
                            _completed = (totalRecordsMatchingSearchCriteria - totalWeDownloadedSuccessfully).Equals(0)
                        };

                        // create new download async object 
                        var localDlSRFobj = new DownLoadFileObject
                        {
                            _rc = rc
                            ,
                            _downLoadPath = srfDownLoadPath
                            ,
                            _recordingLinkURL = videoLinkURL
                            ,
                            _objPI = localObjPI
                            ,
                            _totalWeDownloadedSuccessfully = totalWeDownloadedSuccessfully
                            ,
                            _bgWorkerWebServiceMP3 = _bgWorkerWebService
                            ,
                            _objFileImageInfo = objFileImageInfo
                            ,
                            _srfa = localSRFA
                        };
                        //////////////////////////////////////////////////////////////////////////
                        #endregion

                        lock (_downloadPadLock)
                        {
                            var found = AsyncFileDownLoader(localDlSRFobj);

                            if (found)
                            {
                                Interlocked.Increment(ref _currentDownloadFileCount);
                                Interlocked.Increment(ref totalWeDownloadedSuccessfully);
                            }
                            else
                            {
                                Interlocked.Decrement(ref _callsToDownLoadCount);
                                UpdateEventViewer("Record not found: " + srfDownLoadPath, EventLogEntryType.Error);
                                Log.LogWrite("New callsToDownLoad count: " + _callsToDownLoadCount);
                            }
                        }
                    }
                    else
                    {
                        /*
                         * null != localSRFA && 
                         * !string.IsNullOrEmpty(localSRFA.RecordingFileLocation) || 
                         * localSRFA.RecordingGuid.Equals(Guid.Empty)))
                         */
                        Log.LogWrite("DownloadVideoFile() didn't have a reason to process!");
                        Log.LogWrite("Was null == localSRFA: " + ((null == localSRFA) ? "true" : "false"));
                        Log.LogWrite("Was string.IsNullOrEmpty(localSRFA.RecordingFileLocation): " + ((string.IsNullOrEmpty(localSRFA.RecordingFileLocation)) ? "true" : "false"));
                        Log.LogWrite("Was localSRFA.RecordingGuid.Equals(Guid.Empty): " + ((localSRFA.RecordingGuid.Equals(Guid.Empty)) ? "true" : "false"));
                    }
                }
                catch (Exception ex)
                {
                    _msgs = ErrorMessageString(ex);
                    UpdateEventViewer(_msgs, EventLogEntryType.Error);
                }
                //////////////////////////////////////////////////////////////////////////        
                #endregion
            }
            finally
            {
                Log.LogWrite("Exit DownloadVideoFile()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// Downloads the given file asynchronously
        /// </summary>
        private bool AsyncFileDownLoader(object state)
        {
            var found = false;
            var dObj = state as DownLoadFileObject;

            if (dObj != null)
            {
                using (var wc = new ArchiveWebClient(120000)) // wait 2 minutes...
                {
                    lock (_downloadPadLock)
                    {
                        wc.UseDefaultCredentials = true;
                        wc.DownloadProgressChanged += _downloadProgressChangedHandler;
                        wc.DownloadFileCompleted += _downloadFileCompletedHandler;

                        Uri u;

                        try
                        {
                            u = new Uri(dObj._recordingLinkURL);
                        }
                        catch (Exception ex)
                        {
                            _msgs = string.Format("Error trying to create Uri: {0} Msg: {1} Method: {2}",
                                dObj._recordingLinkURL, ex.Message, ex.TargetSite);
                            UpdateEventViewer(_msgs, EventLogEntryType.Error);
                            _msgs = ErrorMessageString(ex);
                            UpdateEventViewer(_msgs, EventLogEntryType.Warning);
                            return false;
                        }

                        try
                        {
                            {
                                wc.DownloadFileAsync(u, dObj._downLoadPath, dObj);
                                found = true;
                            }
                        }
                        catch (Exception se)
                        {
                            _msgs = ErrorMessageString(se);
                            UpdateEventViewer(_msgs, EventLogEntryType.Warning);
                        }
                    } // exit object lock
                } // exit webclient downloader
            }
            return found;
        }

        /// <summary>
        /// this is the only method that
        /// should be used to release sync
        /// objects that monitor download
        /// activity...
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private static void WcDownloadFileCompleted(object sender, AsyncCompletedEventArgs e)
        {
            using (var wc = (ArchiveWebClient)sender)
            {
                lock (_downloadPadLock)
                {
                    if (wc != null)
                    {
                        // web client is active...
                        if (_cancellationPendingWebService)
                        {
                            Log.LogWrite("WC_DownloadFileCompleted(): canceling pending web service activity...");
                            Log.LogWrite("WC_DownloadFileCompleted(): web client active...");
                            Log.LogWrite("WC_DownloadFileCompleted(): currentDownloadFileCount: " +
                                         _currentDownloadFileCount);
                            Log.LogWrite("WC_DownloadFileCompleted(): callsToDownLoad: " + _callsToDownLoadCount);
                            Log.LogWrite("WC_DownloadFileCompleted(): tracking videosToDownLoad: " +
                                         _videosToDownLoadCount);

                            wc.CancelAsync();

                            // when the process gets canceled we
                            // need to track the currentDownloadFileCount;
                            // when the last file is downloaded, this
                            // value will be one...
                            if (_currentDownloadFileCount < 2)
                            {
                                if (_autoEventAllAudioFilesDownloaded != null)
                                {
                                    //
                                    // release the video download...
                                    // Bug Fix 5779: Archive tool hangs when trying to cancel
                                    // if the search criteria returned a large result set
                                    _autoEventAllAudioFilesDownloaded.Set();
                                }
                                if (_autoEventMultiFileDownload != null)
                                {
                                    // party over, time to stop all downloads...
                                    _autoEventMultiFileDownload.Set();
                                }
                            }
                        }
                    }
                    else
                    {
                        // web client is inactive...
                        if (_cancellationPendingWebService)
                        {
                            Log.LogWrite("WC_DownloadFileCompleted(): canceling pending web service activity...");
                            Log.LogWrite("WC_DownloadFileCompleted(): web client inactive...");
                            Log.LogWrite("WC_DownloadFileCompleted(): currentDownloadFileCount: " +
                                         _currentDownloadFileCount);
                            Log.LogWrite("WC_DownloadFileCompleted(): callsToDownLoad: " + _callsToDownLoadCount);
                            Log.LogWrite("WC_DownloadFileCompleted(): tracking videosToDownLoad: " +
                                         _videosToDownLoadCount);

                            // when the process gets canceled we
                            // need to track the currentDownloadFileCount;
                            // when the last file is downloaded, this
                            // value will be one...
                            if (_currentDownloadFileCount < 2)
                            {
                                if (_autoEventAllAudioFilesDownloaded != null)
                                {
                                    //
                                    // release the video download...
                                    // Bug Fix 5779: Archive tool hangs when trying to cancel
                                    // if the search criteria returned a large result set
                                    _autoEventAllAudioFilesDownloaded.Set();
                                }
                                if (_autoEventMultiFileDownload != null)
                                {
                                    // party over, time to stop all downloads...
                                    _autoEventMultiFileDownload.Set();
                                }
                            }
                        }
                    }

                    //
                    // only store data after we have received the
                    // DownloadCompleted event and no errors occurred...
                    //

                    try
                    {
                        if (null != e)
                        {
                            var dObj = e.UserState as DownLoadFileObject;
                            StoreDownLoadResults(dObj, VerifySenderIsMP3(wc, e));
                        }
                        else
                        {
                            Log.LogWrite("WC_DownloadFileCompleted(): if (null != e) is false...");
                        }
                    }
                    catch (Exception ex)
                    {
                        Log.LogWrite("WC_DownloadFileCompleted(): Error occurred:");
                        Log.LogWrite(ErrorMessageString(ex));
                    }
                    finally
                    {
                        Interlocked.Decrement(ref _currentDownloadFileCount);
                        Interlocked.Decrement(ref _callsToDownLoadCount);
                        if (_totalNumberOfVideoFilesToDownload > _callsToDownLoadCount)
                            Interlocked.Decrement(ref _videosToDownLoadCount);
                    }


                    Log.LogWrite("WC_DownloadFileCompleted(): tracking currentDownloadFileCount: " +
                                 _currentDownloadFileCount);
                    Log.LogWrite("WC_DownloadFileCompleted(): tracking callsToDownLoad: " + _callsToDownLoadCount);
                    Log.LogWrite("WC_DownloadFileCompleted(): tracking videosToDownLoad: " + _videosToDownLoadCount);


                    // interim sync release, this will allow
                    // the download processor to resume...
                    if (_currentDownloadFileCount < _maxNumberOfFilesToDownloadConcurrently)
                        if (_autoEventMaxMultiFileDownloadExceeded != null)
                            // release the hounds...
                            _autoEventMaxMultiFileDownloadExceeded.Set();

                    if ((_callsToDownLoadCount <= _totalNumberOfVideoFilesToDownload) ||
                        (_totalNumberOfVideoFilesToDownload < 1))
                        if (_autoEventAllAudioFilesDownloaded != null)
                            // release the video download...
                            _autoEventAllAudioFilesDownloaded.Set();

                    // this is when all the calls have been
                    // downloaded and we are ready to move
                    // on to the next phase...
                    if (_callsToDownLoadCount < 1)
                        if (_autoEventMultiFileDownload != null)
                            // party over, return control back to the writer...
                            _autoEventMultiFileDownload.Set();

                }
            }
        }

        /// <summary>
        /// primarily used to handle cancelling
        /// the download process when necessary...
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private static void WcDownloadProgressChanged(object sender, DownloadProgressChangedEventArgs e)
        {
            using (var wc = (ArchiveWebClient)sender)
            {
                if (wc != null)
                {
                    if (_cancellationPendingWebService)
                        wc.CancelAsync();

                    if (e.BytesReceived.Equals(0))
                    {
                        lock (e)
                        {
                            // put a call back...
                            Interlocked.Increment(ref _currentDownloadFileCount);
                            Interlocked.Increment(ref _callsToDownLoadCount);
                            // write to event viewer...
                            string downLoadPath = (e.UserState as DownLoadFileObject)._downLoadPath;
                            string m = string.Format("{0} was put back!",
                                downLoadPath.Substring(downLoadPath.LastIndexOf("\\") + 1));
                            UpdateEventViewer(m, EventLogEntryType.Warning);
                        }
                    }
                    else
                    {
                        if (e.TotalBytesToReceive > 0 && e.ProgressPercentage > 99)
                        {
                            string downLoadPath = (e.UserState as DownLoadFileObject)._downLoadPath;
                            string m =
                                string.Format(
                                    "\r\n\t\t\tDownload Progress Update:\r\n\t\t\tFile {0} downloaded -\r\n\t\t\t{1} Bytes expected -\r\n\t\t\t{2} Bytes received -\r\n\t\t\t({3}%)"
                                    , downLoadPath.Substring(downLoadPath.LastIndexOf("\\") + 1)
                                    , e.BytesReceived.ToString("#,#")
                                    , e.TotalBytesToReceive.ToString("#,#")
                                    , e.ProgressPercentage);
                            Log.LogWrite(m);
                        }
                    }
                }
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="dObj"></param>
        private static void StoreDownLoadResults(DownLoadFileObject dObj, bool isMP3)
        {
            string webServiceBackGroundWorkerStatus = "StoreDownLoadResults(): bgworker web service active...";
            if (dObj != null)
            {
                try
                {
                    //
                    // Only update results when an audio file is downloaded;
                    // For now this is valid because we currently include 
                    // all the relevant information about the other file 
                    // types (e.g. SRF) in this download object...
                    //
                    if (isMP3) dObj.StoreFileDownLoadResults(dObj);

                    // give progress report...
                    if (dObj._bgWorkerWebServiceMP3.IsBusy)
                    {
                        dObj._bgWorkerWebServiceMP3.ReportProgress(dObj._totalWeDownloadedSuccessfully
                            , new ObjProgressInfo()
                            {
                                _completed = dObj._objPI._completed
                                ,
                                _fileName = dObj._objPI._fileName
                                ,
                                _fileSize = dObj._objPI._fileSize
                                ,
                                _filesRemaining = dObj._objPI._filesRemaining
                                ,
                                _recCount = dObj._objPI._recCount
                                ,
                                _startup = dObj._objPI._startup
                            });
                    }
                    else
                    {
                        webServiceBackGroundWorkerStatus = "StoreDownLoadResults(): bgworker web service inactive...";
                    }
                }
                catch (Exception ex)
                {
                    _msgs = string.Format("Issue discovered during download file completion event.\r\nNotice: {0}\r\nTarget: {1}"
                        , ex.Message
                        , ex.TargetSite);
                    UpdateEventViewer(_msgs, EventLogEntryType.Warning);
                }
                finally
                {
                    Log.LogWrite(webServiceBackGroundWorkerStatus);
                }
            }
        }

        /// <summary>
        /// is this the MP3 file? we test because all
        /// the details we care about are carried in
        /// the MP3 download object
        /// </summary>
        /// <param name="wc"></param>
        /// <param name="e"></param>
        /// <returns></returns>
        private static bool VerifySenderIsMP3(WebClient wc, AsyncCompletedEventArgs e)
        {
            bool match = false;
            try
            {
                match = _audioExtensionList.Contains(new FileInfo((e.UserState as DownLoadFileObject)._downLoadPath).Extension.ToUpper());
                if (!match) Log.LogWrite("Sender is ***NOT*** an audio file...");
                else Log.LogWrite("Sender is an audio file...");
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                Log.LogWrite(_msgs);
            }
            return match;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="p"></param>
        private static void SaveTransportErrors(string transportError)
        {
            if (!_transportErrors.Contains(transportError))
            {
                Log.LogWrite("SaveTransportErrors: transport error - " + transportError);
                _transportErrors.Add(transportError);
            }
        }

        #region Web Service Callers...
        ////////////////////////////////////////////////////////////////////////// 

        #region Data retrieval web service utilities...

        /// <summary>
        /// 
        /// </summary>
        /// <param name="audioDuplicates"></param>
        /// <returns></returns>
        private int ProcessAudioDuplicates(int audioDuplicates)
        {
            Log.LogWrite("Enter ProcessAudioDuplicates()...");
            try
            {
                //
                // now look for duplicates...
                var query = from v in CallsArray.ToList()
                            let recordingFileLocation = v.RecordingFileLocation
                            where recordingFileLocation != null
                            group v by
                                recordingFileLocation.Substring(recordingFileLocation.LastIndexOf("\\", StringComparison.Ordinal) +
                                                                1)
                                into g
                                where g.Count() > 1
                                select new { FileName = g.Key, FileCount = g.Count() };
                //
                //
                foreach (var item in query)
                {
                    Log.LogWrite(string.Format("CallsArray: FileName {0} exists {1} times", item.FileName, item.FileCount));
                    audioDuplicates += (item.FileCount - 1);
                }

                if (audioDuplicates > 0)
                {
                    // filter duplicates from list

                    var newCallArrayListWithoutDupes = CallsArray
                        .ToList()
                        .GroupBy(g => g.RecordingFileLocation.Substring(g.RecordingFileLocation.LastIndexOf("\\", StringComparison.Ordinal) + 1))
                        .Select(g => g.First()).ToList();

                    if (newCallArrayListWithoutDupes.Any())
                    {
                        // recreate CallsArray without duplicates
                        CallsArray = newCallArrayListWithoutDupes.ConvertAll(i => new RecordedCalls()
                        {
                            CallExpires = i.CallExpires,
                            CallID = i.CallID,
                            CallTime = i.CallTime,
                            CategoryIconUrl = i.CategoryIconUrl,
                            CategoryID = i.CategoryID,
                            CategoryName = i.CategoryName,
                            ChannelName = i.ChannelName,
                            Comments = i.Comments,
                            DiskSize = i.DiskSize,
                            Duration = i.Duration,
                            ExtensionId = i.ExtensionId,
                            ExtnNumber = i.ExtnNumber,
                            FromCallerID = i.FromCallerID,
                            FromNumber = i.FromNumber,
                            ID = i.ID,
                            ISOFileID = i.ISOFileID,
                            Location = i.Location,
                            MD5Hash = i.MD5Hash,
                            RecorderAddress = i.RecorderAddress,
                            RecordingFileLink = i.RecordingFileLink,
                            RecordingFileLocation = i.RecordingFileLocation,
                            SaveRecording = i.SaveRecording,
                            TimeZoneDisplayName = i.TimeZoneDisplayName,
                            ToCallerID = i.ToCallerID,
                            ToDelete = i.ToDelete,
                            ToNumber = i.ToNumber,
                            ExternalLink = i.ExternalLink,
                            DirectionFlag = i.DirectionFlag,
                            CallGuid = i.CallGuid,
                            CallSurveyID = i.CallSurveyID,
                            ExtnDescription = i.ExtnDescription,
                            HasAudioMiningHit = i.HasAudioMiningHit,
                            RedirectFrom = i.RedirectFrom,
                            RedirectTo = i.RedirectTo,
                            SyncStatus = i.SyncStatus
                        }).ToArray();
                    }

                    if (CallsArray != null) Log.LogWrite("1. New CallArray List Count: " + CallsArray.Length);
                }
            }
            finally
            {
                Log.LogWrite("Exit ProcessAudioDuplicates()...");
            }
            return audioDuplicates;
        }

        /// <summary>
        /// 
        /// </summary>
        private void RemoveAllRecordsWithNoRecordingFileLocation()
        {
            Log.LogWrite("Enter RemoveAllRecordsWithNoRecordingFileLocation()...");

            try
            {
                //
                // now look records with no recording file location...
                var query = (from v in CallsArray.ToList()
                             let recordingFileLocation = v.RecordingFileLocation
                             where recordingFileLocation == null
                             select v);

                if (query.Any())
                {
                    var recordedCallsWithRecordingFileLocation =
                        new List<RecordedCalls>(CallsArray)
                            .Where(rfl => !string.IsNullOrEmpty(rfl.RecordingFileLocation))
                            .ToList();

                    // recreate CallsArray with records that have a recording file location
                    CallsArray = recordedCallsWithRecordingFileLocation.ConvertAll(i => new RecordedCalls()
                    {
                        CallExpires = i.CallExpires,
                        CallID = i.CallID,
                        CallTime = i.CallTime,
                        CategoryIconUrl = i.CategoryIconUrl,
                        CategoryID = i.CategoryID,
                        CategoryName = i.CategoryName,
                        ChannelName = i.ChannelName,
                        Comments = i.Comments,
                        DiskSize = i.DiskSize,
                        Duration = i.Duration,
                        ExtensionId = i.ExtensionId,
                        ExtnNumber = i.ExtnNumber,
                        FromCallerID = i.FromCallerID,
                        FromNumber = i.FromNumber,
                        ID = i.ID,
                        ISOFileID = i.ISOFileID,
                        Location = i.Location,
                        MD5Hash = i.MD5Hash,
                        RecorderAddress = i.RecorderAddress,
                        RecordingFileLink = i.RecordingFileLink,
                        RecordingFileLocation = i.RecordingFileLocation,
                        SaveRecording = i.SaveRecording,
                        TimeZoneDisplayName = i.TimeZoneDisplayName,
                        ToCallerID = i.ToCallerID,
                        ToDelete = i.ToDelete,
                        ToNumber = i.ToNumber,
                        ExternalLink = i.ExternalLink,
                        DirectionFlag = i.DirectionFlag,
                        CallGuid = i.CallGuid,
                        CallSurveyID = i.CallSurveyID,
                        ExtnDescription = i.ExtnDescription,
                        HasAudioMiningHit = i.HasAudioMiningHit,
                        RedirectFrom = i.RedirectFrom,
                        RedirectTo = i.RedirectTo,
                        SyncStatus = i.SyncStatus
                    }).ToArray();

                    if (CallsArray != null) Log.LogWrite("2. New CallArray List Count: " + CallsArray.Length);
                }
            }
            finally
            {
                Log.LogWrite("Exit RemoveAllRecordsWithNoRecordingFileLocation()...");
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="videoDuplicates"></param>
        /// <returns></returns>
        private int ProcessVideoDuplicates(int videoDuplicates)
        {
            Log.LogWrite("Enter ProcessVideoDuplicates()...");
            try
            {
                // now look for duplicates...
                var query = from v in ScreenRecordingVideoArray.ToList()
                            let recordingFileLocation = v.RecordingFileLocation
                            where recordingFileLocation != null
                            group v by
                                recordingFileLocation.Substring(
                                    recordingFileLocation.LastIndexOf("\\", StringComparison.Ordinal) + 1)
                                into g
                                where g.Count() > 1
                                select new { FileName = g.Key, FileCount = g.Count() };

                foreach (var item in query)
                {
                    Log.LogWrite(string.Format("ScreenRecordingVideoArray: FileName {0} exists {1} times", item.FileName, item.FileCount));
                    videoDuplicates += (item.FileCount - 1);
                }

                if (videoDuplicates > 0)
                {
                    // filter duplicates from list
                    var newScreenRecordingVideoListWithoutDupes = ScreenRecordingVideoArray
                        .ToList()
                        .GroupBy(g => g.RecordingFileLocation.Substring(g.RecordingFileLocation.LastIndexOf("\\", StringComparison.Ordinal) + 1))
                        .Select(g => g.First()).ToList();

                    if (newScreenRecordingVideoListWithoutDupes.Any())
                    {
                        // recreate ScreenRecordingVideoArray without duplicates
                        ScreenRecordingVideoArray = newScreenRecordingVideoListWithoutDupes.ConvertAll(i => new ScreenRecordingForArchival()
                        {
                            AudioPosition = i.AudioPosition,
                            CallId = i.CallId,
                            Comments = i.Comments,
                            ContentLength = i.ContentLength,
                            DiskSize = i.DiskSize,
                            Duration = i.Duration,
                            EmployeeId = i.EmployeeId,
                            EndPos = i.EndPos,
                            EndTime = i.EndTime,
                            MD5Hash = i.MD5Hash,
                            MovieFileLocation = i.MovieFileLocation,
                            RecordingExpires = i.RecordingExpires,
                            RecordingFileLocation = i.RecordingFileLocation,
                            RecordingGuid = i.RecordingGuid,
                            RecordingId = i.RecordingId,
                            ScreenRecordingVideoLink = i.ScreenRecordingVideoLink,
                            StartPos = i.StartPos,
                            StartTime = i.StartTime,
                            ToDelete = i.ToDelete
                        }).ToArray();
                    }

                    if (ScreenRecordingVideoArray != null)
                        Log.LogWrite("1. New ScreenRecordingVideoArray List Count: " + ScreenRecordingVideoArray.Length);
                }
            }
            finally
            {
                Log.LogWrite("Exit ProcessVideoDuplicates()...");
            }

            return videoDuplicates;
        }

        /// <summary>
        /// 
        /// </summary>
        private void RemoveAllVideosWithNoRecordingFileLocation()
        {
            Log.LogWrite("Enter RemoveAllVideosWithNoRecordingFileLocation()...");
            try
            {
                //
                // now look records with no recording file location...
                var query = (from v in ScreenRecordingVideoArray.ToList()
                             let recordingFileLocation = v.RecordingFileLocation
                             where recordingFileLocation != null
                             select v).ToList();

                if (query.Any())
                {
                    var newScreenRecordingVideoListWithoutDupes =
                        new List<ScreenRecordingForArchival>(ScreenRecordingVideoArray)
                            .Where(rfl => !string.IsNullOrEmpty(rfl.RecordingFileLocation))
                            .ToList();

                    if (newScreenRecordingVideoListWithoutDupes.Any())
                    {
                        // recreate ScreenRecordingVideoArray without duplicates
                        ScreenRecordingVideoArray =
                            newScreenRecordingVideoListWithoutDupes.ConvertAll(i => new ScreenRecordingForArchival()
                            {
                                AudioPosition = i.AudioPosition,
                                CallId = i.CallId,
                                Comments = i.Comments,
                                ContentLength = i.ContentLength,
                                DiskSize = i.DiskSize,
                                Duration = i.Duration,
                                EmployeeId = i.EmployeeId,
                                EndPos = i.EndPos,
                                EndTime = i.EndTime,
                                MD5Hash = i.MD5Hash,
                                MovieFileLocation = i.MovieFileLocation,
                                RecordingExpires = i.RecordingExpires,
                                RecordingFileLocation = i.RecordingFileLocation,
                                RecordingGuid = i.RecordingGuid,
                                RecordingId = i.RecordingId,
                                ScreenRecordingVideoLink = i.ScreenRecordingVideoLink,
                                StartPos = i.StartPos,
                                StartTime = i.StartTime,
                                ToDelete = i.ToDelete
                            }).ToArray();
                    }

                    if (ScreenRecordingVideoArray != null)
                        Log.LogWrite("2. New ScreenRecordingVideoArray List Count: " + ScreenRecordingVideoArray.Length);
                }
            }
            finally
            {
                Log.LogWrite("Exit RemoveAllVideosWithNoRecordingFileLocation()...");
            }
        }

        /// <summary>
        /// TODO: Needs to be updated for handling
        /// records that include video files.
        /// Primary task is to retrieve all content in
        /// recycle bin regardless of date...
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        private void SearchRecycleBin(ArchiveWS classicArchiveWS)
        {
            RecycleBinCallsArray = classicArchiveWS.GetRecordedCallsInRecycleBin(
                ObjFileImageInfo.UserName
                , ObjFileImageInfo.PassWord
                , ObjFileImageInfo.IsAdmin
                , _includeArchivedCalls
                );


            var tmp = new List<RecordedCalls>(CallsArray);
            tmp.AddRange(RecycleBinCallsArray);

            CallsArray = tmp.ConvertAll(i =>
                                        new RecordedCalls()
                                        {
                                            CallExpires = i.CallExpires
                                            ,
                                            CallID = i.CallID
                                            ,
                                            CallTime = i.CallTime
                                            ,
                                            CategoryIconUrl = i.CategoryIconUrl
                                            ,
                                            CategoryID = i.CategoryID
                                            ,
                                            CategoryName = i.CategoryName
                                            ,
                                            ChannelName = i.ChannelName
                                            ,
                                            Comments = i.Comments
                                            ,
                                            DiskSize = i.DiskSize
                                            ,
                                            Duration = i.Duration
                                            ,
                                            ExtensionId = i.ExtensionId
                                            ,
                                            ExtnNumber = i.ExtnNumber
                                            ,
                                            FromCallerID = i.FromCallerID
                                            ,
                                            FromNumber = i.FromNumber
                                            ,
                                            ID = i.ID
                                            ,
                                            ISOFileID = i.ISOFileID
                                            ,
                                            Location = i.Location
                                            ,
                                            MD5Hash = i.MD5Hash
                                            ,
                                            RecorderAddress = i.RecorderAddress
                                            ,
                                            RecordingFileLink = i.RecordingFileLink
                                            ,
                                            RecordingFileLocation = i.RecordingFileLocation
                                            ,
                                            SaveRecording = i.SaveRecording
                                            ,
                                            TimeZoneDisplayName = i.TimeZoneDisplayName
                                            ,
                                            ToCallerID = i.ToCallerID
                                            ,
                                            ToDelete = i.ToDelete
                                            ,
                                            ToNumber = i.ToNumber
                                            ,
                                            ExternalLink = i.ExternalLink
                                            ,
                                            DirectionFlag = i.DirectionFlag

                                        }).ToArray();
        }

        /// <summary>
        /// 
        /// </summary>
        private static void WaitForDownloadsToComplete()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter WaitForDownloadsToComplete()...");
            try
            {
                Log.LogWrite("1. !!!!!!!!!! GetSQLData(): _autoEventMultiFileDownload.WaitOne - hold !!!!!!!!!!");
                Log.LogWrite("Was the download canceled? " + _cancellationPendingWebService);
                bool success = false;
                success = _autoEventMultiFileDownload.WaitOne(!_cancellationPendingWebService ? TimeSpan.FromSeconds(150) : TimeSpan.FromSeconds(10));

                string comment = success ? "We have received the release command..." : "No, will wait for another 150 seconds and that's it...";
                Log.LogWrite("2. !!!!!!!!!! GetSQLData(): _autoEventMultiFileDownload.WaitOne - results? " + comment);
                if (success.Equals(false))
                {
                    // we will manually call the method that
                    // handles releasing the thread sync objects
                    WcDownloadFileCompleted(new ArchiveWebClient(), null); 
                    success = _autoEventMultiFileDownload.WaitOne(!_cancellationPendingWebService ? TimeSpan.FromSeconds(150) : TimeSpan.FromSeconds(10));
                    comment = success ? "We have received the release command..." : "No, will try to handle the problem downloads later...";
                    Log.LogWrite("2a. !!!!!!!!!! GetSQLData(): _autoEventMultiFileDownload.WaitOne - results? " + comment);
                }
                Log.LogWrite("3. !!!!!!!!!! GetSQLData(): _autoEventMultiFileDownload.WaitOne - release !!!!!!!!!!");
            }
            finally
            {
                var ts = stopwatch.Elapsed;
                Log.LogWrite("Exit WaitForDownloadsToComplete()... " + string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                                                                           , ts.Hours
                                                                           , ts.Minutes
                                                                           , ts.Seconds
                                                                           , ts.Milliseconds / 10));
            }
        }

        #region Populate the download array objects...
        //////////////////////////////////////////////////////////////////////////

        #region Populate Audio Objects

        /// <summary>
        /// 
        /// </summary>
        /// <param name="attempts"></param>
        /// <param name="done"></param>
        /// <param name="classicArchiveWS"> </param>
        private void PopulateCallsArrayObject(ref int attempts, ref bool done, ArchiveWS classicArchiveWS)
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter PopulateCallsArrayObject()...");
            try
            {
                while (!done && attempts < _maxAttemptsToContactServer && !_cancellationPendingWebService)
                {
                    try
                    {
                        var startTime = ObjFileImageInfo.StartDateRange;
                        var endTime = ObjFileImageInfo.EndDateRange;

                        Interlocked.Increment(ref attempts);

                        // setup arrays...
                        CallsArray = RecycleBinCallsArray = new RecordedCalls[0];

                        if (!_archiveRecycleBinContents)
                        {
                            _autoEventRetrieveSqlResultSetInChunks.Reset();
                            Log.LogWrite(
                                "1. *#*#*#*#*# PopulateCallsArrayObjectInHourlyChunks(): _autoEventRetrieveSqlResultSetInChunks.WaitOne - holding *#*#*#*#*#");

                            PopulateCallsArrayObjectInHourlyChunks(classicArchiveWS, endTime, startTime);

                            _autoEventRetrieveSqlResultSetInChunks.WaitOne();
                            Log.LogWrite(
                                "2. *#*#*#*#*# PopulateCallsArrayObjectInHourlyChunks(): _autoEventRetrieveSqlResultSetInChunks.WaitOne - released *#*#*#*#*#");

                            done = true;
                        }
                        else
                        {
                            SearchRecycleBin(classicArchiveWS);
                        }

                        //
                        // do we have any data?
                        if (CallsArray != null && CallsArray.Any())
                        {
                            //
                            // do we have at least 1 record with a Recording file location?
                            var foundRecordingFileLocation =
                                CallsArray.ToList().Any(
                                    rfl => string.IsNullOrEmpty(rfl.RecordingFileLocation).Equals(false));

                            //
                            // if we don't, wait 7 seconds...
                            if (!foundRecordingFileLocation)
                            {
                                _msgs = _archiveRecycleBinContents
                                            ? @"Recycle Bin: RecordingFileLocation not found: wait 7 seconds and try retrieving data again..."
                                            : @"Call Detail: RecordingFileLocation not found: wait 7 seconds and try retrieving data again...";
                                Log.LogWrite(_msgs);
                                Thread.Sleep(7000);
                            }

                            done = foundRecordingFileLocation;
                        }
                        else
                        {
                            // 
                            // no data so were done...
                            done = true;
                        }
                    }
                    catch (FaultException fe)
                    {
                        #region error...

                        //
                        // Bug #3308: Error Message in Archiver Console - The error needs to 
                        // be a more  user friendly error message that maybe says 
                        // "Please contact <someone> for access to the archival tool" or 
                        // something to that effect - 
                        //
                        // 20100224 - Note that this exception was being thrown when the 
                        //          underlying data adapter requested a column that was not
                        //          in the result set. The ws call is returning "InternalException"
                        //          by default when an unrecognized error occurs...
                        //
                        _msgs = string.Format(RES.Resources.RES_InvalidCredentialsLoginFailedEventViewer
                            , fe.Message
                            , fe.InnerException
                            , fe.StackTrace);

                        if (fe.Message.ToUpper().Contains("INVALIDCREDENTIALS"))
                        {
                            // stop now...
                            attempts += _maxAttemptsToContactServer;
                        }

                        UpdateEventViewer(_msgs, EventLogEntryType.Error);
                        //
                        // not sure if this is necessary, but we will let him try again
                        //
                        if (attempts >= _maxAttemptsToContactServer)
                        {
                            _msgs = string.Format(RES.Resources.RES_InvalidCredentialsLoginFailed);
                            throw new SRIPArchiveClientFormException(_msgs);
                        }
                        else
                            Thread.Sleep(5000);

                        #endregion
                    }
                    catch (Exception e)
                    {
                        #region error...

                        //
                        // Bug #3308: Error Message in Archiver Console - The error needs to 
                        // be a more  user friendly error message that maybe says 
                        // "Please contact <someone> for access to the archival tool" or 
                        // something to that effect
                        //
                        _msgs = string.Format(RES.Resources.RES_WebServiceRequestFailedEventViewer
                            , e.Message
                            , e.InnerException
                            , attempts
                            , _maxAttemptsToContactServer);


                        if (e.Message.ToUpper().Contains("INVALIDCREDENTIALS"))
                        {
                            // stop now...
                            attempts += _maxAttemptsToContactServer;
                        }

                        UpdateEventViewer(_msgs, EventLogEntryType.Error);
                        if (attempts >= _maxAttemptsToContactServer)
                        {
                            _msgs = string.Format(RES.Resources.RES_WebServiceRequestFailed);
                            throw new SRIPArchiveClientFormException(_msgs);
                        }
                        else
                            Thread.Sleep(OneSecond);

                        #endregion
                    }
                } // end while
            }
            finally
            {
                var ts = stopwatch.Elapsed;
                Log.LogWrite("Exit PopulateCallsArrayObject()... "
                             + string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                                   , ts.Hours, ts.Minutes, ts.Seconds, ts.Milliseconds / 10));
            }
        }

        /// <summary>
        /// Take user request and break up into
        /// hourly chunks to try and minimize
        /// network timeouts; also limits request
        /// to 90 days. Average process time for each 
        /// chunk is 3s; 24 hours takes  approximately 72s; 
        /// 30 days takes approximately 36min. These times will
        /// vary of course depending on the result set 
        /// returned for the chunk...
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        /// <param name="endTime"></param>
        /// <param name="startTime"></param>
        private void PopulateCallsArrayObjectInHourlyChunks(ArchiveWS classicArchiveWS
                                                            , DateTime endTime, DateTime startTime)
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter PopulateCallsArrayObjectInHourlyChunks()...");
            try
            {
                var callsArrayChunks = new List<RecordedCalls>(CallsArray);
                //
                // limit search to 60 days, that equates to 1440 hours...
                if (endTime.Subtract(startTime).Days > _archiveNumberOfDaysLimit)
                {
                    var over = endTime.Subtract(startTime).Days - (_archiveNumberOfDaysLimit);
                    startTime = startTime.AddDays(over);
                    //
                    // reset start time...
                    ObjFileImageInfo.StartDateRange = startTime;

                    Log.LogWrite(string.Format("Request is {0} days over maximum. Reset start time to: {1}", over, startTime));
                }

                var filter = new CalendarPeriodCollectorFilter();
                var dateRange = new CalendarTimeRange(startTime, endTime);
                var timePeriodCollector = new CalendarPeriodCollector(filter, dateRange);
                timePeriodCollector.CollectHours();

                Log.LogWrite(string.Format("Request Range: {0}"
                    , timePeriodCollector.Limits));

                Log.LogWrite(
                    string.Format(
                        "===== {0} Day(s) ===== {1} Hour(s) ===== {2} Minute(s) ===== {3} Second(s) ===== {4} Chunk(s) ===== "
                        , timePeriodCollector.Limits.Duration.Days
                        , timePeriodCollector.Limits.Duration.Hours
                        , timePeriodCollector.Limits.Duration.Minutes
                        , timePeriodCollector.Limits.Duration.Seconds
                        , timePeriodCollector.Periods.Count));

                if (timePeriodCollector.Periods.Count > 0)
                {
                    //
                    // step 1: Get Opening Partial Data, e.g. 2012-06-01 07:15:00->2012-06-01 07:59:59
                    //
                    GetOpeningPartialPeriodAudioData(classicArchiveWS, callsArrayChunks, timePeriodCollector);
                    //
                    // step 2: Get All Data Per Found Period, e.g. 2012-06-01 08:00:00->2012-06-30 14:59:59
                    //
                    GetPeriodAudioData(classicArchiveWS, callsArrayChunks, timePeriodCollector);
                    //
                    // step 3: Get Closing Partial Data, e.g. 2012-06-30 15:00:00->2012-06-30 14:30:00
                    //
                    GetClosingPartialPeriodAudioData(classicArchiveWS, callsArrayChunks, timePeriodCollector);
                    //
                    // step 4: All Results... 
                    //
                    PackagePeriodDataIntoCallsArray(callsArrayChunks);
                }
                else
                {
                    //
                    // user request is for less than 1 hour of data
                    //
                    CallsArray = classicArchiveWS.GetRecordedCallsToBeArchived(
                        ObjFileImageInfo.UserName
                        , ObjFileImageInfo.PassWord
                        , ObjFileImageInfo.StartDateRange
                        , ObjFileImageInfo.EndDateRange
                        , ObjFileImageInfo.IsAdmin
                        , _includeArchivedCalls
                        );

                    Log.LogWrite(string.Format("Period: {0} - {1} - Records: {2}",
                        ObjFileImageInfo.StartDateRange.ToString("u", CultureInfo.InvariantCulture)
                        , ObjFileImageInfo.EndDateRange.ToString("u", CultureInfo.InvariantCulture)
                        , CallsArray.Count()));
                }
            }
            finally
            {
                var ts = stopwatch.Elapsed;

                Log.LogWrite("Exit PopulateCallsArrayObjectInHourlyChunks()... "
                             + string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                                   , ts.Hours, ts.Minutes, ts.Seconds, ts.Milliseconds / 10));

                _autoEventRetrieveSqlResultSetInChunks.Set();
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        /// <param name="callsArrayChunks"></param>
        /// <param name="timePeriodCollector"></param>
        private void GetOpeningPartialPeriodAudioData(ArchiveWS classicArchiveWS, List<RecordedCalls> callsArrayChunks, CalendarPeriodCollector timePeriodCollector)
        {
            //
            // step 1: Get Intital Partial Data, e.g. 2012-06-01 07:15:00->2012-06-01 07:59:59
            //

            Log.LogWrite(@"Step 1: Get Opening Partial Data Audio.");

            var done = false;
            var retryDataPeriodCounter = 0;
            var recordedCallsToBeArchived = new RecordedCalls[] { };

            while (!done && retryDataPeriodCounter < ChunkRetryLimit)
            {
                if (_cancellationPendingWebService) break;

                recordedCallsToBeArchived = classicArchiveWS.GetRecordedCallsToBeArchived(
                    ObjFileImageInfo.UserName
                    , ObjFileImageInfo.PassWord
                    , ((timePeriodCollector.Limits.Start.Second > 0) || (timePeriodCollector.Limits.Start.Minute > 0))
                          ? timePeriodCollector.Limits.Start
                          : timePeriodCollector.Limits.Start.AddSeconds(1)
                    , timePeriodCollector.Periods.Start.AddSeconds(-1)
                    , ObjFileImageInfo.IsAdmin
                    , _includeArchivedCalls);

                if (recordedCallsToBeArchived != null && recordedCallsToBeArchived.Any())
                {
                    //
                    // do we have at least 1 record with a Recording file location?
                    var foundRecordingFileLocation = recordedCallsToBeArchived
                        .ToList()
                        .Any(rfl => !string.IsNullOrEmpty(rfl.RecordingFileLocation));
                    //
                    // if we don't, wait and retry...
                    if (!foundRecordingFileLocation)
                    {
                        _msgs =
                            @"Call Detail (Hourly): RecordingFileLocation not found: wait " +
                            ChunkRetryWaitTimeInMilliseconds + @" ms and try retrieving data again...";
                        Log.LogWrite(_msgs);
                        Thread.Sleep(ChunkRetryWaitTimeInMilliseconds);
                    }
                    //
                    // results
                    done = foundRecordingFileLocation;
                }
                else
                {
                    //
                    // no data...
                    retryDataPeriodCounter = ChunkRetryLimit;
                }

                Interlocked.Increment(ref retryDataPeriodCounter);

            } // end while


            if (!done)
            {
                var msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period...";
                var recCount = recordedCallsToBeArchived == null ? 0 : recordedCallsToBeArchived.Count();
                if (recCount > 0)
                    msg =
                        @"Period: {0} - {1} ----> Found {2} record(s) for this period but none with a recording file location...";

                Log.LogWrite(string.Format(msg
                    , ((timePeriodCollector.Limits.Start.Second > 0) || (timePeriodCollector.Limits.Start.Minute > 0))
                          ? timePeriodCollector.Limits.Start.ToString("s")
                          : timePeriodCollector.Limits.Start.AddSeconds(1).ToString("s")
                    , timePeriodCollector.Periods.Start.AddSeconds(-1).ToString("s")
                    , recCount));
            }
            else
            {
                callsArrayChunks.AddRange(recordedCallsToBeArchived);
            }

            if (recordedCallsToBeArchived != null)
            {
                Log.LogWrite(string.Format("Period: {0} - {1} - Records: {2} - Initial Total: {3}",
                    ((timePeriodCollector.Limits.Start.Second > 0) || (timePeriodCollector.Limits.Start.Minute > 0))
                        ? timePeriodCollector.Limits.Start.ToString("s")
                        : timePeriodCollector.Limits.Start.AddSeconds(1).ToString("s")
                    , timePeriodCollector.Periods.Start.AddSeconds(-1).ToString("s")
                    , recordedCallsToBeArchived.Count()
                    , callsArrayChunks.Count));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        /// <param name="callsArrayChunks"></param>
        /// <param name="timePeriodCollector"></param>
        private void GetPeriodAudioData(ArchiveWS classicArchiveWS, List<RecordedCalls> callsArrayChunks, CalendarPeriodCollector timePeriodCollector)
        {
            //
            // step 2: Get All Data Per Found Period, e.g. 2012-06-01 08:00:00->2012-06-30 14:59:59
            //
            Log.LogWrite(@"Step 2: Get All Data Per Selected Period.");
            foreach (var dataPeriod in timePeriodCollector.Periods)
            {
                if (_cancellationPendingWebService) break;

                var done = false;
                var retryDataPeriodCounter = 0;
                var recordedCallsToBeArchived = new RecordedCalls[] { };

                while (!done && retryDataPeriodCounter < ChunkRetryLimit)
                {
                    if (_cancellationPendingWebService) break;

                    recordedCallsToBeArchived = classicArchiveWS.GetRecordedCallsToBeArchived(ObjFileImageInfo.UserName
                        , ObjFileImageInfo.PassWord
                        , dataPeriod.Start
                        , dataPeriod.End
                        , ObjFileImageInfo.IsAdmin
                        , _includeArchivedCalls);

                    if (recordedCallsToBeArchived != null && recordedCallsToBeArchived.Any())
                    {
                        //
                        // do we have at least 1 record with a Recording file location?
                        var foundRecordingFileLocation = recordedCallsToBeArchived
                            .ToList()
                            .Any(rfl => !string.IsNullOrEmpty(rfl.RecordingFileLocation));
                        //
                        // if we don't, wait and retry...
                        if (!foundRecordingFileLocation)
                        {
                            _msgs =
                                @"Call Detail (Hourly): RecordingFileLocation not found: wait " +
                                ChunkRetryWaitTimeInMilliseconds + @" ms and try retrieving data again...";
                            Log.LogWrite(_msgs);
                            Thread.Sleep(ChunkRetryWaitTimeInMilliseconds);
                        }
                        //
                        // results
                        done = foundRecordingFileLocation;
                    }
                    else
                    {
                        //
                        // no data...
                        retryDataPeriodCounter = ChunkRetryLimit;
                    }

                    Interlocked.Increment(ref retryDataPeriodCounter);

                } // while (!done && retryDataPeriodCounter < 3)


                if (!done)
                {
                    var msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period...";
                    var recCount = recordedCallsToBeArchived == null ? 0 : recordedCallsToBeArchived.Count();
                    if (recCount > 0)
                        msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period but none with a recording file location...";

                    Log.LogWrite(string.Format(msg
                        , dataPeriod.Start.ToString("s")
                        , dataPeriod.End.ToString("s")
                        , recCount));

                    continue;
                }

                callsArrayChunks.AddRange(recordedCallsToBeArchived);

                Log.LogWrite(string.Format(
                    "Period: {0} - {1} - Records: {2} - Running Total: {3}",
                    dataPeriod.Start.ToString("s")
                    , dataPeriod.End.ToString("s")
                    , recordedCallsToBeArchived.Count()
                    , callsArrayChunks.Count));
            } // end foreach (var dataPeriod in timePeriodCollector.Periods)
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        /// <param name="callsArrayChunks"></param>
        /// <param name="timePeriodCollector"></param>
        private void GetClosingPartialPeriodAudioData(ArchiveWS classicArchiveWS, List<RecordedCalls> callsArrayChunks, CalendarPeriodCollector timePeriodCollector)
        {
            // step 3: Get Closing Partial Data, e.g. 2012-06-30 15:00:00->2012-06-30 15:30:00
            //

            Log.LogWrite(@"Step 3: Get Closing Partial Data.");

            var done = false;
            var retryDataPeriodCounter = 0;
            var recordedCallsToBeArchived = new RecordedCalls[] { };

            while (!done && retryDataPeriodCounter < ChunkRetryLimit)
            {
                if (_cancellationPendingWebService) break;

                recordedCallsToBeArchived = classicArchiveWS.GetRecordedCallsToBeArchived(ObjFileImageInfo.UserName
                    , ObjFileImageInfo.PassWord
                    , timePeriodCollector.Periods.End.AddSeconds(1)
                    , timePeriodCollector.Limits.End
                    , ObjFileImageInfo.IsAdmin
                    , _includeArchivedCalls);

                if (recordedCallsToBeArchived != null && recordedCallsToBeArchived.Any())
                {
                    //
                    // do we have at least 1 record with a Recording file location?
                    var foundRecordingFileLocation = recordedCallsToBeArchived
                        .ToList()
                        .Any(rfl => !string.IsNullOrEmpty(rfl.RecordingFileLocation));
                    //
                    // if we don't, wait and retry...
                    if (!foundRecordingFileLocation)
                    {
                        _msgs =
                            @"Call Detail (Hourly): RecordingFileLocation not found: wait " +
                            ChunkRetryWaitTimeInMilliseconds + @" ms and try retrieving data again...";
                        Log.LogWrite(_msgs);
                        Thread.Sleep(ChunkRetryWaitTimeInMilliseconds);
                    }
                    //
                    // results
                    done = foundRecordingFileLocation;
                }
                else
                {
                    //
                    // no data...
                    retryDataPeriodCounter = ChunkRetryLimit;
                }

                Interlocked.Increment(ref retryDataPeriodCounter);

            } // while (!done && retryDataPeriodCounter < 3)


            if (!done)
            {
                var msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period...";
                var recCount = recordedCallsToBeArchived == null ? 0 : recordedCallsToBeArchived.Count();
                if (recCount > 0)
                    msg =
                        @"Period: {0} - {1} ----> Found {2} record(s) for this period but none with a recording file location...";

                Log.LogWrite(string.Format(msg
                    , timePeriodCollector.Periods.End.AddSeconds(1).ToString("s")
                    , timePeriodCollector.Limits.End.ToString("s")
                    , recCount));
            }
            else
            {
                callsArrayChunks.AddRange(recordedCallsToBeArchived);
            }

            if (recordedCallsToBeArchived != null)
            {
                Log.LogWrite(string.Format("Period: {0} - {1} - Records: {2} - Final Total: {3}",
                    timePeriodCollector.Periods.End.AddSeconds(1).ToString("s")
                    , timePeriodCollector.Limits.End.ToString("s")
                    , recordedCallsToBeArchived.Count()
                    , callsArrayChunks.Count));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="callsArrayChunks"></param>
        private void PackagePeriodDataIntoCallsArray(List<RecordedCalls> callsArrayChunks)
        {
            Log.LogWrite(@"Step 4: Package Period Data in CallsArray Object.");
            CallsArray = callsArrayChunks.ConvertAll(i => new RecordedCalls()
            {
                CallExpires = i.CallExpires,
                CallID = i.CallID,
                CallTime = i.CallTime,
                CategoryIconUrl = i.CategoryIconUrl,
                CategoryID = i.CategoryID,
                CategoryName = i.CategoryName,
                ChannelName = i.ChannelName,
                Comments = i.Comments,
                DiskSize = i.DiskSize,
                Duration = i.Duration,
                ExtensionId = i.ExtensionId,
                ExtnNumber = i.ExtnNumber,
                FromCallerID = i.FromCallerID,
                FromNumber = i.FromNumber,
                ID = i.ID,
                ISOFileID = i.ISOFileID,
                Location = i.Location,
                MD5Hash = i.MD5Hash,
                RecorderAddress = i.RecorderAddress,
                RecordingFileLink = i.RecordingFileLink,
                RecordingFileLocation = i.RecordingFileLocation,
                SaveRecording = i.SaveRecording,
                TimeZoneDisplayName = i.TimeZoneDisplayName,
                ToCallerID = i.ToCallerID,
                ToDelete = i.ToDelete,
                ToNumber = i.ToNumber,
                ExternalLink = i.ExternalLink,
                DirectionFlag = i.DirectionFlag,
                CallGuid = i.CallGuid,
                CallSurveyID = i.CallSurveyID,
                ExtnDescription = i.ExtnDescription,
                HasAudioMiningHit = i.HasAudioMiningHit,
                RedirectFrom = i.RedirectFrom,
                RedirectTo = i.RedirectTo,
                SyncStatus = i.SyncStatus
            }).ToArray();
        }

        #endregion

        #region Populate Video Objects

        /// <summary>
        /// 
        /// </summary>
        /// <param name="attempts"></param>
        /// <param name="done"></param>
        /// <param name="classicArchiveWS"> </param>
        private void PopulateScreenRecordingVideoArrayObject(ref int attempts
                                                             , ref bool done
                                                             , ArchiveWS classicArchiveWS)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter PopulateScreenRecordingVideoArrayObject()...");

            try
            {
                while (!done && attempts < _maxAttemptsToContactServer && !_cancellationPendingWebService)
                {
                    try
                    {
                        var startTime = ObjFileImageInfo.StartDateRange;
                        var endTime = ObjFileImageInfo.EndDateRange;

                        Interlocked.Increment(ref attempts);

                        // setup arrays...
                        ScreenRecordingVideoArray = new ScreenRecordingForArchival[0];

                        _autoEventRetrieveSqlResultSetInChunks.Reset();
                        Log.LogWrite(
                            "1. *#*#*#*#*# PopulateScreenRecordingVideoArrayObjectInHourlyChunks(): _autoEventRetrieveSqlResultSetInChunks.WaitOne - holding *#*#*#*#*#");

                        PopulateScreenRecordingVideoArrayObjectInHourlyChunks(classicArchiveWS, endTime, startTime);

                        _autoEventRetrieveSqlResultSetInChunks.WaitOne();
                        Log.LogWrite(
                            "2. *#*#*#*#*# PopulateScreenRecordingVideoArrayObjectInHourlyChunks(): _autoEventRetrieveSqlResultSetInChunks.WaitOne - released *#*#*#*#*#");

                        done = true;
                    }
                    catch (FaultException fe)
                    {
                        #region error...

                        //
                        // Bug #3308: Error Message in Archiver Console - The error needs to 
                        // be a more  user friendly error message that maybe says 
                        // "Please contact <someone> for access to the archival tool" or 
                        // something to that effect - 
                        //
                        // 20100224 - Note that this exception was being thrown when the 
                        //          underlying data adapter requested a column that was not
                        //          in the result set. The ws call is returning "InternalException"
                        //          by default when an unrecognized error occurs...
                        //
                        _msgs = string.Format(RES.Resources.RES_InvalidCredentialsLoginFailedEventViewer
                            , fe.Message
                            , fe.InnerException
                            , fe.StackTrace);

                        if (fe.Message.ToUpper().Contains("INVALIDCREDENTIALS"))
                        {
                            // stop now...
                            attempts += _maxAttemptsToContactServer;
                        }

                        UpdateEventViewer(_msgs, EventLogEntryType.Error);
                        //
                        // not sure if this is necessary, but we will let him try again
                        //
                        if (attempts >= _maxAttemptsToContactServer)
                        {
                            _msgs = string.Format(RES.Resources.RES_InvalidCredentialsLoginFailed);
                            throw new SRIPArchiveClientFormException(_msgs);
                        }
                        else
                            Thread.Sleep(5000);

                        #endregion
                    }
                    catch (Exception e)
                    {
                        #region error...

                        //
                        // Bug #3308: Error Message in Archiver Console - The error needs to 
                        // be a more  user friendly error message that maybe says 
                        // "Please contact <someone> for access to the archival tool" or 
                        // something to that effect
                        //
                        _msgs = string.Format(RES.Resources.RES_WebServiceRequestFailedEventViewer
                            , e.Message
                            , e.InnerException
                            , attempts
                            , _maxAttemptsToContactServer);

                        if (e.Message.ToUpper().Contains("INVALIDCREDENTIALS"))
                        {
                            // stop now...
                            attempts += _maxAttemptsToContactServer;
                        }

                        UpdateEventViewer(_msgs, EventLogEntryType.Error);
                        if (attempts >= _maxAttemptsToContactServer)
                        {
                            _msgs = string.Format(RES.Resources.RES_WebServiceRequestFailed);
                            throw new SRIPArchiveClientFormException(_msgs);
                        }
                        else
                            Thread.Sleep(OneSecond);

                        #endregion
                    }
                }
            }
            finally
            {
                var ts = stopwatch.Elapsed;
                Log.LogWrite("Exit PopulateScreenRecordingVideoArrayObject()... " + string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                                                                                        , ts.Hours
                                                                                        , ts.Minutes
                                                                                        , ts.Seconds
                                                                                        , ts.Milliseconds / 10));
            }
        }

        /// <summary>
        /// Take user request and break up into
        /// hourly chunks to try and minimize
        /// network timeouts; also limits request
        /// to 90 days. Average process time for each 
        /// chunk is 3s; 24 hours takes  approximately 72s; 
        /// 30 days takes approximately 36min. These times will
        /// vary of course depending on the result set 
        /// returned for the chunk...  
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        /// <param name="endTime"></param>
        /// <param name="startTime"></param>
        private void PopulateScreenRecordingVideoArrayObjectInHourlyChunks(ArchiveWS classicArchiveWS
                                                                           , DateTime endTime
                                                                           , DateTime startTime)
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter PopulateScreenRecordingVideoArrayObjectInHourlyChunks()...");
            try
            {
                var screenRecordingVideoArrayChunks = new List<ScreenRecordingForArchival>(ScreenRecordingVideoArray);
                //
                // limit search to 60 days, that equates to 1440 hours...
                if (endTime.Subtract(startTime).Days > _archiveNumberOfDaysLimit)
                {
                    var over = endTime.Subtract(startTime).Days - (_archiveNumberOfDaysLimit);
                    startTime = startTime.AddDays(over);
                    //
                    // reset start time...
                    ObjFileImageInfo.StartDateRange = startTime;

                    Log.LogWrite(string.Format("Request is {0} days over maximum. Reset start time to: {1}", over, startTime));
                }

                var filter = new CalendarPeriodCollectorFilter();
                var dateRange = new CalendarTimeRange(startTime, endTime);
                var timePeriodCollector = new CalendarPeriodCollector(filter, dateRange);
                timePeriodCollector.CollectHours();

                Log.LogWrite(string.Format("Request Range: {0}"
                    , timePeriodCollector.Limits));

                Log.LogWrite(
                    string.Format(
                        "===== {0} Day(s) ===== {1} Hour(s) ===== {2} Minute(s) ===== {3} Second(s) ===== {4} Chunk(s) ===== "
                        , timePeriodCollector.Limits.Duration.Days
                        , timePeriodCollector.Limits.Duration.Hours
                        , timePeriodCollector.Limits.Duration.Minutes
                        , timePeriodCollector.Limits.Duration.Seconds
                        , timePeriodCollector.Periods.Count));

                if (timePeriodCollector.Periods.Count > 0)
                {
                    //
                    // step 1: Get Opening Partial Data, e.g. 2012-06-01 07:15:00->2012-06-01 07:59:59
                    //
                    GetOpeningPartialPeriodVideoData(classicArchiveWS, screenRecordingVideoArrayChunks, timePeriodCollector);
                    //
                    // step 2: Get All Data Per Found Period, e.g. 2012-06-01 08:00:00->2012-06-30 14:59:59
                    //
                    GetPeriodVideoData(classicArchiveWS, screenRecordingVideoArrayChunks, timePeriodCollector);
                    //
                    // step 3: Get Closing Partial Data, e.g. 2012-06-30 15:00:00->2012-06-30 14:30:00
                    //
                    GetClosingPartialPeriodVideoData(classicArchiveWS, screenRecordingVideoArrayChunks, timePeriodCollector);
                    //
                    // step 4: All Results... 
                    //
                    PackagePeriodDataIntoScreenRecordingVideoArray(screenRecordingVideoArrayChunks);
                }
                else
                {
                    ScreenRecordingVideoArray = classicArchiveWS.GetScreenRecordingsToBeArchived(
                        ObjFileImageInfo.UserName
                        , ObjFileImageInfo.PassWord
                        , ObjFileImageInfo.StartDateRange
                        , ObjFileImageInfo.EndDateRange
                        , ObjFileImageInfo.IsAdmin);

                    Log.LogWrite(string.Format("Period: {0} - {1} - Records: {2}",
                        ObjFileImageInfo.StartDateRange.ToString("u", CultureInfo.InvariantCulture)
                        , ObjFileImageInfo.EndDateRange.ToString("u", CultureInfo.InvariantCulture)
                        , ScreenRecordingVideoArray.Count()));
                }
            }
            finally
            {
                var ts = stopwatch.Elapsed;

                Log.LogWrite("Exit PopulateScreenRecordingVideoArrayObjectInHourlyChunks()... "
                             + string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                                   , ts.Hours, ts.Minutes, ts.Seconds, ts.Milliseconds / 10));

                _autoEventRetrieveSqlResultSetInChunks.Set();
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        /// <param name="screenRecordingVideoArrayChunks"></param>
        /// <param name="timePeriodCollector"></param>
        private void GetOpeningPartialPeriodVideoData(ArchiveWS classicArchiveWS
                                                      , List<ScreenRecordingForArchival> screenRecordingVideoArrayChunks
                                                      , CalendarPeriodCollector timePeriodCollector)
        {
            //
            // step 1: Get Intital Partial Data, e.g. 2012-06-01 07:15:00->2012-06-01 07:59:59
            //

            Log.LogWrite(@"Step 1: Get Opening Partial Data Video.");

            var done = false;
            var retryDataPeriodCounter = 0;
            var screenRecordingsToBeArchived = new ScreenRecordingForArchival[] { };

            while (!done && retryDataPeriodCounter < ChunkRetryLimit)
            {
                if (_cancellationPendingWebService) break;

                screenRecordingsToBeArchived = classicArchiveWS.GetScreenRecordingsToBeArchived(
                    ObjFileImageInfo.UserName
                    , ObjFileImageInfo.PassWord
                    , ((timePeriodCollector.Limits.Start.Second > 0) || (timePeriodCollector.Limits.Start.Minute > 0))
                          ? timePeriodCollector.Limits.Start
                          : timePeriodCollector.Limits.Start.AddSeconds(1)
                    , timePeriodCollector.Periods.Start.AddSeconds(-1)
                    , ObjFileImageInfo.IsAdmin);

                if (screenRecordingsToBeArchived != null && screenRecordingsToBeArchived.Any())
                {
                    //
                    // do we have at least 1 record with a Recording file location?
                    var foundRecordingFileLocation = screenRecordingsToBeArchived
                        .ToList()
                        .Any(rfl => !string.IsNullOrEmpty(rfl.RecordingFileLocation));

                    //
                    // if we don't, wait 5 seconds...
                    if (!foundRecordingFileLocation)
                    {
                        _msgs =
                            @"Screen Recordings (Hourly): RecordingFileLocation not found: wait " +
                            ChunkRetryWaitTimeInMilliseconds + @" ms and try retrieving data again...";
                        Log.LogWrite(_msgs);
                        Thread.Sleep(ChunkRetryWaitTimeInMilliseconds);
                    }

                    done = foundRecordingFileLocation;
                }
                else
                {
                    //
                    // no data...
                    retryDataPeriodCounter = ChunkRetryLimit;
                }

                Interlocked.Increment(ref retryDataPeriodCounter);

            }

            if (!done)
            {
                var msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period...";
                var recCount = screenRecordingsToBeArchived == null ? 0 : screenRecordingsToBeArchived.Count();
                if (recCount > 0)
                    msg =
                        @"Period: {0} - {1} ----> Found {2} record(s) for this period but none with a recording file location...";

                Log.LogWrite(string.Format(msg
                    , ((timePeriodCollector.Limits.Start.Second > 0) || (timePeriodCollector.Limits.Start.Minute > 0))
                          ? timePeriodCollector.Limits.Start.ToString("s")
                          : timePeriodCollector.Limits.Start.AddSeconds(1).ToString("s")
                    , timePeriodCollector.Periods.Start.AddSeconds(-1).ToString("s")
                    , recCount));
            }
            else
            {
                screenRecordingVideoArrayChunks.AddRange(screenRecordingsToBeArchived);
            }


            if (screenRecordingsToBeArchived != null)
            {
                Log.LogWrite(string.Format("Period: {0} - {1} - Records: {2} - Initial Total: {3}",
                    ((timePeriodCollector.Limits.Start.Second > 0) || (timePeriodCollector.Limits.Start.Minute > 0))
                        ? timePeriodCollector.Limits.Start.ToString("s")
                        : timePeriodCollector.Limits.Start.AddSeconds(1).ToString("s")
                    , timePeriodCollector.Periods.Start.AddSeconds(-1).ToString("s")
                    , screenRecordingsToBeArchived.Count()
                    , screenRecordingVideoArrayChunks.Count));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        /// <param name="screenRecordingVideoArrayChunks"></param>
        /// <param name="timePeriodCollector"></param>
        private void GetPeriodVideoData(ArchiveWS classicArchiveWS
                                        , List<ScreenRecordingForArchival> screenRecordingVideoArrayChunks
                                        , CalendarPeriodCollector timePeriodCollector)
        {
            //
            // step 2: Get All Data Per Found Period, e.g. 2012-06-01 08:00:00->2012-06-30 14:59:59
            //
            Log.LogWrite(@"Step 2: Get All Data Per Selected Period.");

            foreach (var dataPeriod in timePeriodCollector.Periods)
            {
                if (_cancellationPendingWebService) break;

                var done = false;
                var retryDataPeriodCounter = 0;
                var screenRecordingsToBeArchived = new ScreenRecordingForArchival[] { };

                while (!done && retryDataPeriodCounter < ChunkRetryLimit)
                {
                    if (_cancellationPendingWebService) break;

                    screenRecordingsToBeArchived = classicArchiveWS.GetScreenRecordingsToBeArchived(
                        ObjFileImageInfo.UserName
                        , ObjFileImageInfo.PassWord
                        , dataPeriod.Start
                        , dataPeriod.End
                        , ObjFileImageInfo.IsAdmin);

                    if (screenRecordingsToBeArchived != null && screenRecordingsToBeArchived.Any())
                    {
                        //
                        // do we have at least 1 record with a Recording file location?
                        var foundRecordingFileLocation = screenRecordingsToBeArchived
                            .ToList()
                            .Any(rfl => !string.IsNullOrEmpty(rfl.RecordingFileLocation));

                        //
                        // if we don't, wait 5 seconds...
                        if (!foundRecordingFileLocation)
                        {
                            _msgs =
                                @"Screen Recordings (Hourly): RecordingFileLocation not found: wait " +
                                ChunkRetryWaitTimeInMilliseconds + @" ms and try retrieving data again...";
                            Log.LogWrite(_msgs);
                            Thread.Sleep(ChunkRetryWaitTimeInMilliseconds);
                        }

                        done = foundRecordingFileLocation;
                    }
                    else
                    {
                        //
                        // no data...
                        retryDataPeriodCounter = ChunkRetryLimit;
                    }

                    Interlocked.Increment(ref retryDataPeriodCounter);

                } // end while (!done && retryDataPeriodCounter < 3)

                if (!done)
                {
                    var msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period...";
                    var recCount = screenRecordingsToBeArchived == null ? 0 : screenRecordingsToBeArchived.Count();
                    if (recCount > 0)
                        msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period but none with a recording file location...";

                    Log.LogWrite(string.Format(msg
                        , dataPeriod.Start.ToString("s")
                        , dataPeriod.End.ToString("s")
                        , recCount));

                    continue;
                }

                screenRecordingVideoArrayChunks.AddRange(screenRecordingsToBeArchived);

                Log.LogWrite(string.Format(
                    "Period: {0} - {1} - Records: {2} - Running Total: {3}",
                    dataPeriod.Start.ToString("s")
                    , dataPeriod.End.ToString("s")
                    , screenRecordingsToBeArchived.Count()
                    , screenRecordingVideoArrayChunks.Count));

            } // end foreach (var dataPeriod in timePeriodCollector.Periods)
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="classicArchiveWS"> </param>
        /// <param name="screenRecordingVideoArrayChunks"></param>
        /// <param name="timePeriodCollector"></param>
        private void GetClosingPartialPeriodVideoData(ArchiveWS classicArchiveWS
                                                      , List<ScreenRecordingForArchival> screenRecordingVideoArrayChunks
                                                      , CalendarPeriodCollector timePeriodCollector)
        {
            //
            // step 3: Get Closing Partial Data, e.g. 2012-06-30 15:00:00->2012-06-30 15:30:00
            //

            Log.LogWrite(@"Step 3: Get Closing Partial Data.");

            var done = false;
            var retryDataPeriodCounter = 0;
            var screenRecordingsToBeArchived = new ScreenRecordingForArchival[] { };

            while (!done && retryDataPeriodCounter < ChunkRetryLimit)
            {
                if (_cancellationPendingWebService) break;

                screenRecordingsToBeArchived =
                    classicArchiveWS.GetScreenRecordingsToBeArchived(ObjFileImageInfo.UserName
                        , ObjFileImageInfo.PassWord
                        , timePeriodCollector.Periods.End.AddSeconds(1)
                        , timePeriodCollector.Limits.End
                        , ObjFileImageInfo.IsAdmin);

                if (screenRecordingsToBeArchived != null && screenRecordingsToBeArchived.Any())
                {
                    //
                    // do we have at least 1 record with a Recording file location?
                    var foundRecordingFileLocation = screenRecordingsToBeArchived
                        .ToList()
                        .Any(rfl => !string.IsNullOrEmpty(rfl.RecordingFileLocation));

                    //
                    // if we don't, wait 5 seconds...
                    if (!foundRecordingFileLocation)
                    {
                        _msgs =
                            @"Screen Recordings (Hourly): RecordingFileLocation not found: wait " +
                            ChunkRetryWaitTimeInMilliseconds + @" ms and try retrieving data again...";
                        Log.LogWrite(_msgs);
                        Thread.Sleep(ChunkRetryWaitTimeInMilliseconds);
                    }

                    done = foundRecordingFileLocation;
                }
                else
                {
                    //
                    // no data...
                    retryDataPeriodCounter = ChunkRetryLimit;
                }

                Interlocked.Increment(ref retryDataPeriodCounter);
            }

            if (!done)
            {
                var msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period...";
                var recCount = screenRecordingsToBeArchived == null ? 0 : screenRecordingsToBeArchived.Count();
                if (recCount > 0)
                    msg = @"Period: {0} - {1} ----> Found {2} record(s) for this period but none with a recording file location...";

                Log.LogWrite(string.Format(msg
                    , timePeriodCollector.Periods.End.AddSeconds(1).ToString("s")
                    , timePeriodCollector.Limits.End.ToString("s")
                    , recCount));
            }
            else
            {

                screenRecordingVideoArrayChunks.AddRange(screenRecordingsToBeArchived);
            }

            if (screenRecordingsToBeArchived != null)
            {
                Log.LogWrite(string.Format("Period: {0} - {1} - Records: {2} - Final Total: {3}",
                    timePeriodCollector.Periods.End.AddSeconds(1).ToString("s")
                    , timePeriodCollector.Limits.End.ToString("s")
                    , screenRecordingsToBeArchived.Count()
                    , screenRecordingVideoArrayChunks.Count));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="screenRecordingVideoArrayChunks"></param>
        private void PackagePeriodDataIntoScreenRecordingVideoArray(List<ScreenRecordingForArchival> screenRecordingVideoArrayChunks)
        {
            Log.LogWrite(@"Step 4: Package Period Data in ScreenRecordingVideoArray Object.");
            ScreenRecordingVideoArray = screenRecordingVideoArrayChunks.ConvertAll(i => new ScreenRecordingForArchival()
            {
                AudioPosition = i.AudioPosition,
                CallId = i.CallId,
                Comments = i.Comments,
                ContentLength = i.ContentLength,
                DiskSize = i.DiskSize,
                Duration = i.Duration,
                EmployeeId = i.EmployeeId,
                EndPos = i.EndPos,
                EndTime = i.EndTime,
                MD5Hash = i.MD5Hash,
                MovieFileLocation = i.MovieFileLocation,
                RecordingExpires = i.RecordingExpires,
                RecordingFileLocation = i.RecordingFileLocation,
                RecordingGuid = i.RecordingGuid,
                RecordingId = i.RecordingId,
                ScreenRecordingVideoLink = i.ScreenRecordingVideoLink,
                StartPos = i.StartPos,
                StartTime = i.StartTime,
                ToDelete = i.ToDelete
            }).ToArray();
        }

        #endregion

        ////[ End Populate the download array objects ]///////////////////////////
        #endregion

        #endregion

        ////[ End Web Service Callers ]//////////////////////////////////////////////
        #endregion

        #region Utilities...

        /// <summary>
        /// 
        /// </summary>
        /// <param name="bytes"></param>
        /// <returns></returns>
        private string ConvertBytesToString(long bytes)
        {
            if (bytes > (1024 * 1024 * 1024)) return ConvertBytesToGigabytes(bytes);
            else if (bytes > (1024 * 1024)) return ConvertBytesToMegabytes(bytes);
            else return ConvertBytesToKilobytes(bytes);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="bytes"></param>
        /// <returns></returns>
        private string ConvertBytesToKilobytes(long bytes)
        {
            return (bytes / 1024f).ToString(CultureInfo.InvariantCulture) + "KB";
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="bytes"></param>
        /// <returns></returns>
        private string ConvertBytesToMegabytes(long bytes)
        {
            return ((bytes / 1024f) / 1024f).ToString(CultureInfo.InvariantCulture) + "MB";
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="bytes"></param>
        /// <returns></returns>
        private string ConvertBytesToGigabytes(long bytes)
        {
            return (((bytes / 1024f) / 1024f) / 1024f).ToString(CultureInfo.InvariantCulture) + "GB";
        }

        /// <summary>
        /// Helper method that does a lookup in
        /// the video files array object for the
        /// item that belongs the the provided
        /// call ID. If nothing is found, we
        /// will return a default, unusable object...
        /// </summary>
        /// <param name="listOfScreenRecordings"></param>
        /// <param name="callID"></param>
        /// <returns></returns>
        private static ScreenRecordingForArchival GetVideoByCallId(List<ScreenRecordingForArchival> listOfScreenRecordings
                                                                    , int callID)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter GetVideoByCallId()...");
            ScreenRecordingForArchival localSRFA = null;

            try
            {
                if (null != listOfScreenRecordings)
                {
                    Log.LogWrite("Perform lookup for SRFA object that matches the callID: " + callID);
                    localSRFA = listOfScreenRecordings.Find(i => i.CallId.Equals(callID));

                    if (null == localSRFA)
                    {
                        Log.LogWrite("No SRFA object found that matches the callID: " + callID);
                    }
                    else
                    {
                        Log.LogWrite("Found SRFA object that matches the callID: " + callID + " Recording: " + localSRFA.RecordingFileLocation);
                    }
                }
                else
                {
                    Log.LogWrite("listOfScreenRecordings is null...");
                }
            }
            catch (Exception ex)
            {
                string m = ErrorMessageString(ex);
                Log.LogWrite(m);
            }
            finally
            {
                var ts = stopwatch.Elapsed;
                Log.LogWrite("Exit GetVideoByCallId()... " + string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                                                                   , ts.Hours
                                                                   , ts.Minutes
                                                                   , ts.Seconds
                                                                   , ts.Milliseconds / 10));
            }
            return localSRFA ?? CreateDefaultVideoObject();
        }
        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private static ScreenRecordingForArchival CreateDefaultVideoObject()
        {
            return new ScreenRecordingForArchival
            {
                RecordingFileLocation = string.Empty
                ,
                RecordingId = -1
                ,
                RecordingGuid = Guid.Empty.ToString()
                ,
                AudioPosition = -1
                ,
                StartPos = -1
                ,
                EndPos = -1
            };
        }

        /// <summary>
        /// create ISO sortable file name
        /// </summary>
        /// <param name="outputLocationPath"></param>
        /// <param name="seq"></param>
        /// <param name="setDate"></param>
        /// <returns></returns>
        private static string CreateISOImageOutputFileName(string outputLocationPath, string seq, bool setDate)
        {
            var fileName = string.Empty;
            var fixISOFileBaseName = _outputISOFileName;
            var currentDateTime = _holdDateTimeForName;

            while (true)
            {
                // insure we are writing to a ISO file...
                if (_outputISOFileName.IndexOf('.') > 0)
                {
                    fixISOFileBaseName = _outputISOFileName.Remove(_outputISOFileName.IndexOf('.'));
                }

                fixISOFileBaseName += ".iso";
                //
                // this is used to allow multiple iso files
                // to keep the same name except for the sequence                
                // value, i.e. userName_yyyy_mm_ddThhmmss_seq_text.iso
                // seq is only inserted when creating multiple iso files...
                //
                currentDateTime = setDate ? DateTime.Now : _holdDateTimeForName;

                fileName = (outputLocationPath
                            + (currentDateTime.ToString("s")
                               + (string.IsNullOrEmpty(seq) ? "" : "_" + seq)
                               + (string.IsNullOrEmpty(_outputISOFileName) ? "" : "_")).Replace(":", string.Empty)
                            + fixISOFileBaseName)
                    .Replace('-', '_');

                if (!new FileInfo(fileName).Exists)
                {
                    _holdDateTimeForName = currentDateTime;
                    break;
                }

                // if we are here we need a new date...
                setDate = true;
            }

            return fileName;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="file"></param>
        /// <returns></returns>
        private static string ComputeMD5Hash(string file)
        {
            string rv = string.Empty;
            try
            {
                if (File.Exists(file))
                {
                    System.Security.Cryptography.MD5 md5 = System.Security.Cryptography.MD5.Create();
                    using (FileStream fileStream = File.OpenRead(file))
                    {
                        byte[] fileHash = md5.ComputeHash(fileStream);
                        StringBuilder stringBuilder = new StringBuilder();
                        for (int i = 0; i < fileHash.Length; Interlocked.Increment(ref i))
                        {
                            stringBuilder.Append(fileHash[i].ToString("X2"));
                        }
                        rv = stringBuilder.ToString();
                    }
                }
            }
            catch { }
            return rv;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="callArrayValue"></param>
        /// <param name="recordedCallValue"></param>
        /// <returns></returns>
        private bool CompareMD5Hash(string callArrayValue, string recordedCallValue)
        {
            bool bEqual = false;
            if (callArrayValue.Length == recordedCallValue.Length)
            {
                int i = 0;
                while ((i < callArrayValue.Length) && (callArrayValue[i] == recordedCallValue[i]))
                {
                    i += 1;
                }
                if (i == callArrayValue.Length)
                {
                    bEqual = true;
                }
            }
            return bEqual;
        }

        #endregion

        #endregion

        ////[ End Phase 1 - Retrieving Data via Web Services ]/////////////////////
        #endregion


        #region Phase 2 - Populate ISO Image Repository...
        //////////////////////////////////////////////////////////////////////////

        #region Background Workers...

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        void BgWorkerAddFilesToImageRepositoryDoWork(object sender, DoWorkEventArgs e)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            try
            {
                Log.LogWrite("Enter BgWorkerAddFilesToImageRepositoryDoWork()...");
                //_autoEventZeroByteFileDownload.Reset();
                _autoEventCreateIsoImageRepository.Reset();
                _cancellationPendingAddingFilesToImageRepository = false;

                WriteTransportErrorsToEventViewer();
                ParsePathsAndFileNames();
                e.Result = "Success";
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                UpdateEventViewer(_msgs, EventLogEntryType.Error);

                if (!e.Cancel) _bgWorkerAddFilesToImageRepository.CancelAsync();
                e.Cancel = true;
                _cancellationPendingAddingFilesToImageRepository = true;
                e.Result = "File Download Failure";
                _bgWorkerErrorMsgs = ex.Message;
            }
            finally
            {
                e.Cancel = _bgWorkerAddFilesToImageRepository.CancellationPending;
                Log.LogWrite("Exit BgWorkerAddFilesToImageRepositoryDoWork()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        void BgWorkerAddFilesToImageRepositoryProgressChanged(object sender, ProgressChangedEventArgs e)
        {
            try
            {
                ObjProgressInfo opi = e.UserState as ObjProgressInfo;

                int pos = (int)((double)e.ProgressPercentage / double.Parse(opi._recCount.ToString()) * 100);
                toolStripProgressBar.Value = pos * 2;

                toolStripStatusLabel.Text = string.Format(RES.Resources.RES_FileCountFilesRemainingPctCompletedFileSizeTimeRemaining
                    , opi._recCount
                    , opi._filesRemaining
                    , (toolStripProgressBar.Value / 2).ToString()
                    , opi._fileSize
                    , TimeRemainingEstimate(_totalTasksToProcess, (Interlocked.Increment(ref _totalTasksProcessed)))
                    );
            }
            catch { /*do nothing...*/ }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        void BgWorkerAddFilesToImageRepositoryRunWorkerCompleted(object sender, RunWorkerCompletedEventArgs e)
        {
            // 
            // wait for path information to be processed...
            Log.LogWrite("1. ENDING-PHASE-2 BgWorkerAddFilesToImageRepositoryDoWork(): _autoEventCreateIsoImageRepository.WaitOne - hold XXXXXXXXXX");
            _autoEventCreateIsoImageRepository.WaitOne();
            Log.LogWrite("2. END-PHASE-2 BgWorkerAddFilesToImageRepositoryDoWork(): _autoEventCreateIsoImageRepository.WaitOne - released XXXXXXXXXX");

            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter BgWorkerAddFilesToImageRepositoryRunWorkerCompleted()...");
            try
            {
                _bgWorkerAddFilesToImageRepository.DoWork -= BgWorkerAddFilesToImageRepositoryDoWork;
                _bgWorkerAddFilesToImageRepository.RunWorkerCompleted -= BgWorkerAddFilesToImageRepositoryRunWorkerCompleted;
                _bgWorkerAddFilesToImageRepository.ProgressChanged -= BgWorkerAddFilesToImageRepositoryProgressChanged;
                _elapsedIsoCreationTime.Stop();

                if (e.Cancelled || _cancellationPendingAddingFilesToImageRepository)
                {
                    _msgs = string.Format(RES.Resources.RES_ParsingFilesCancelledDueTo
                        , FormatElapsedTime(_elapsedIsoCreationTime)
                        , _bgWorkerErrorMsgs);
                    PopulateStatusTextBox(_msgs, true);
                    RestoreUI();
                    return;
                }

                _msgs = string.Format(RES.Resources.RES_ParsingFilesCompleted   //"Parsing files completed - elapsed time: {0} "
                    , FormatElapsedTime(_elapsedIsoCreationTime));
                PopulateStatusTextBox(_msgs, true);

                ProcessImageRepositoryObject();
            }
            finally
            {
                Log.LogWrite("Exit BgWorkerAddFilesToImageRepositoryRunWorkerCompleted()... " + FormatElapsedTime(stopwatch));
            }
        }

        #region BgWorkerAddFilesToImageRepository Calls When Completed...

        /// <summary>
        /// this is the critical loop for
        /// creating iso images; we just call 
        /// this method to start the iso
        /// creation process...
        /// </summary>
        private void ProcessImageRepositoryObject()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter ProcessImageRepositoryObject()...");

            _autoEventIsoWriterCriticalLoop.Reset();

            try
            {
                try
                {
                    InitRepository();
                }
                catch (Exception ex)
                {
                    Log.LogWrite("Error 1: " + ex.Message);
                    throw;
                }

                try
                {
                    RunISOWriterProcessor();
                }
                catch (Exception ex)
                {
                    Log.LogWrite("Error 2: " + ex.Message);
                    throw;
                }
            }
            finally
            {
                Log.LogWrite("Exit ProcessImageRepositoryObject()... " + FormatElapsedTime(stopwatch));
                _autoEventIsoWriterCriticalLoop.Set();
            }
        }

        #endregion


        ////[ End Background Workers ISO Image Repository ]///////////////////////
        #endregion

        #region Support Methods...

        /// <summary>
        /// add the files we downloaded to the
        /// the image repository for the ISO writer        
        /// </summary>
        private void ParsePathsAndFileNames()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter ParsePathsAndFileNames()...");

            try
            {
                #region initialise...
                int recCount = ObjFileImageInfo.PathsAndFileNames.Count;
                int recFound = 0;

                Log.LogWrite(string.Format("PathsAndFileNames count: {0}", recCount));

                _totalTasksToProcess = recCount; // add the index.csv file
                _totalTasksProcessed = 0;

                // now that we can create multiple iso files,
                // we need to be sure and include an index with
                // each image we create...
                var trackIndexItems = 0;
                var listIndexData = new List<FileImageInfo.IndexData>();

                // track items in ObjFileImageInfo.ArchiveTableList in a special list
                var listArchiveDataTableContent = new List<FileImageInfo.ArchiveData>();

                ObjProgressInfo objPI = new ObjProgressInfo
                {
                    _fileName = string.Empty
                    ,
                    _completed = false
                    ,
                    _fileSize = 0
                    ,
                    _filesRemaining = recCount
                    ,
                    _recCount = recCount
                    ,
                    _startup = false
                };
                #endregion

                #region Dump the list of files to download...
                //////////////////////////////////////////////////////////////
                try
                {
                    int counter = 0;
                    Action<string> logFileNames = fileNames =>
                                                  Log.LogWrite(string.Format("[Rec: {0}, Bytes: {2}] {1}"
                                                      , Interlocked.Increment(ref counter)
                                                      , fileNames
                                                      , (new FileInfo(fileNames).Length).ToString("#,#")));
                    ObjFileImageInfo.PathsAndFileNames.ForEach(logFileNames);
                }
                catch { }
                //////////////////////////////////////////////////////////////
                #endregion

                #region Comments...
                //////////////////////////////////////////////////////////////
                /* 
                 * If the number of files downloaded is greater than the 
                 * ArchiveTableList/IndexFileData count, we have records 
                 * with multiple files embedded in the details. For now
                 * that means a single call record has at least 2 files -
                 * an MP3 file and a SRF file.
                 * 
                 * We will adjust the code to handle this parse in
                 * such a way that if we need to add another file
                 * type (e.g. Speech Pack, Audio Mining, etc.), it
                 * will be a *little* easier to do it...                 
                 * 
                 */
                //////////////////////////////////////////////////////////////
                #endregion

                int databaseIndex = 0; // these entries coincide with archive db content...
                for (int fileIndex = 0; fileIndex < recCount; Interlocked.Increment(ref fileIndex))
                {
                    if (_bgWorkerAddFilesToImageRepository.CancellationPending) return;

                    var path = ObjFileImageInfo.PathsAndFileNames[fileIndex];

                    if (path.Contains(RES.Resources.RES_IndexCSVFileName)) continue; // shouldn't happen anymore...  
                    if (!_audioExtensionList.Contains(new FileInfo(path).Extension.ToUpper())) continue; // only accept audio files...

                    var audioFileName = ObjFileImageInfo.ArchiveTableList[databaseIndex].MP3DownLoadPathAndFileName;
                    var videoFileName = ObjFileImageInfo.ArchiveTableList[databaseIndex].SRFDownLoadPathAndFileName;

                    lock (_trackDownloadFileSizeAccum)
                    {
                        listIndexData.Add(ObjFileImageInfo.IndexFileData[databaseIndex]);
                        listArchiveDataTableContent.Add(ObjFileImageInfo.ArchiveTableList[databaseIndex]);
                    }

                    AddDownloadedFileToISOBuildList(recCount
                        , ref recFound
                        , ref trackIndexItems
                        , listIndexData
                        , listArchiveDataTableContent
                        , objPI
                        , fileIndex
                        , path
                        , audioFileName
                        , videoFileName);

                    Interlocked.Increment(ref databaseIndex);
                }

                //
                // Always insure we have an index file!            
                // 2 concerns:
                //  If the finalIndex is > 0 create an index.
                //  If we only have one image, create an index.            
                //
                int finalIndex;
                lock (_trackDownloadFileSizeAccum)
                {
                    finalIndex = (recCount - listIndexData.Count);
                }

                lock (_trackDownloadFileSizeAccum)
                {
                    Log.LogWrite(
                        string.Format(
                            "\r\n\tFinal Rec Count: {0}\r\n\tFinal ListIndex Count: {1}\r\n\tFinal Index Count: {2}\r\n\tDownload FSz: {3}\r\n\tCapacity: {4}\r\n\tTrackIndex Count: {5}\r\n\tIsoImageIndex: {6}\r\n\tImage(s): {7}"
                            , recCount
                            , listIndexData.Count
                            , finalIndex
                            , _downloadFileSizeRunningTotal.ToString("#,#")
                            , _formatFileSize.ToString("#,#")
                            , trackIndexItems
                            , _isoImageRepositoryIndex
                            , _dictionaryOfArchiveDataTableContent.Count));
                }


                if ((finalIndex > 0) || _isoImageRepositoryIndex.Equals(0))
                {
                    string finalPath = ObjFileImageInfo.PathsAndFileNames[0];
                    string finalIndexName;
                    lock (_createIndexNameLock)
                    {
                        finalIndexName = CreateIndexTextValue(trackIndexItems) + "_" +
                                         RES.Resources.RES_IndexCSVFileName;
                        CreateArchiveIndexFile(listIndexData, finalIndexName);
                    }
                    string finalNewIndexFile = new FileInfo(finalPath).DirectoryName + "\\" + finalIndexName;
                    if (File.Exists(finalNewIndexFile))
                    {
                        Log.LogWrite("Added new item, " + finalNewIndexFile + ", to ImageRepository");
                        AddFileToImageRepository(finalNewIndexFile);
                    }
                    else
                    {
                        Log.LogWrite("finalNewIndexFile, " + finalNewIndexFile + ", not found...");
                    }
                    lock (_objectLock)
                    {
                        _dictionaryOfArchiveDataTableContent.Add(trackIndexItems,
                            new List<FileImageInfo.ArchiveData>(
                                listArchiveDataTableContent));
                        Log.LogWrite("Added new item to _dictionaryOfArchiveDataTableContent");
                        foreach (var dtc in _dictionaryOfArchiveDataTableContent)
                        {
                            Log.LogWrite("DTC Key: " + dtc.Key);
                        }
                    }
                }
            }
            finally
            {
                Log.LogWrite("Exit ParsePathsAndFileNames()... " + FormatElapsedTime(stopwatch));
                _autoEventCreateIsoImageRepository.Set();
            }
        }

        /// <summary>
        /// isolate process for parsing downloaded
        /// files for adding to ISO image builder list...
        /// </summary>
        /// <param name="recCount"></param>
        /// <param name="recFound"></param>
        /// <param name="trackIndexItems"></param>
        /// <param name="listIndexData"></param>
        /// <param name="listArchiveDataTableContent"></param>
        /// <param name="objPI"></param>
        /// <param name="fileIndex"></param>
        /// <param name="path"></param>
        /// <param name="audioFileName"></param>
        /// <param name="videoFileName"></param>
        private void AddDownloadedFileToISOBuildList(int recCount
                                                     , ref int recFound
                                                     , ref int trackIndexItems
                                                     , List<FileImageInfo.IndexData> listIndexData
                                                     , List<FileImageInfo.ArchiveData> listArchiveDataTableContent
                                                     , ObjProgressInfo objPI
                                                     , int fileIndex
                                                     , string path
                                                     , string audioFileName
                                                     , string videoFileName)
        {
            var audioFileValidated = false;
            var videoFileValidated = false;
            var fileDictionary = new Dictionary<SupportedDownloadFileTypes, string>();

            if (!string.IsNullOrEmpty(audioFileName) &&
                _validFileExtensionsList.Contains(new FileInfo(audioFileName).Extension.ToUpper()))
            {
                fileDictionary.Add(SupportedDownloadFileTypes.MP3, audioFileName);
            }
            if (!string.IsNullOrEmpty(videoFileName) &&
                _validFileExtensionsList.Contains(new FileInfo(videoFileName).Extension.ToUpper()))
            {
                fileDictionary.Add(SupportedDownloadFileTypes.SRF, videoFileName);
            }

            foreach (KeyValuePair<SupportedDownloadFileTypes, string> kvp in fileDictionary)
            {
                switch (kvp.Key)
                {
                    case SupportedDownloadFileTypes.MP3:
                        {
                            #region Gather Audio Data...

                            //////////////////////////////////////////////////
                            if (kvp.Value != null && kvp.Value.Equals(audioFileName))
                            {
                                if (audioFileName != null && File.Exists(audioFileName))
                                {
                                    Interlocked.Increment(ref recFound);
                                    audioFileValidated = true;
                                    var audioFileSize = new FileInfo(audioFileName).Length;

                                    #region progress bar stuff...

                                    objPI._fileName = audioFileName;
                                    objPI._recCount = recCount; // total number of records to process...
                                    objPI._filesRemaining = recCount - (recFound);
                                    objPI._fileSize = audioFileSize;
                                    objPI._startup = (recFound == 1) ? true : false;
                                    objPI._completed = objPI._filesRemaining == 0 ? true : false;

                                    // if the filesize == 0, handle it...
                                    if (audioFileSize < 1)
                                    {
                                        ZeroByteFilesHandler(listIndexData, objPI, fileIndex);
                                    }
                                    else
                                    {
                                        lock (_trackDownloadFileSizeAccum)
                                        {
                                            _downloadFileSizeRunningTotal += objPI._fileSize;
                                        }
                                    }

                                    #endregion
                                }
                                else if (Directory.Exists(path))
                                {
                                    AddFolderToImageRepository(path);
                                }

                                // submit progress report....
                                this._bgWorkerAddFilesToImageRepository.ReportProgress(recFound,
                                    // xfer ownership of shared data...
                                    new ObjProgressInfo()
                                    {
                                        _completed = objPI._completed
                                        ,
                                        _fileName = objPI._fileName
                                        ,
                                        _fileSize = objPI._fileSize
                                        ,
                                        _filesRemaining =
                                            objPI._filesRemaining
                                        ,
                                        _recCount = objPI._recCount
                                        ,
                                        _startup = objPI._startup
                                    });
                            }
                            //////////////////////////////////////

                            #endregion
                        }
                        break;

                    case SupportedDownloadFileTypes.SRF:
                        {
                            #region Gather Video Data...

                            //////////////////////////////////////
                            if (kvp.Value != null && kvp.Value.Equals(videoFileName))
                            {
                                if (ObjFileImageInfo.PathsAndFileNames.Contains(videoFileName))
                                {
                                    if (videoFileName != null && File.Exists(videoFileName))
                                    {
                                        Interlocked.Increment(ref recFound);
                                        videoFileValidated = true;
                                        var videoFileSize = new FileInfo(videoFileName).Length;

                                        #region progress bar stuff...

                                        objPI._fileName = videoFileName;
                                        objPI._recCount = recCount; // total number of records to process...
                                        objPI._filesRemaining = recCount - (recFound);
                                        objPI._fileSize = videoFileSize;
                                        objPI._startup = (recFound == 1) ? true : false;
                                        objPI._completed = objPI._filesRemaining == 0 ? true : false;
                                        lock (_trackDownloadFileSizeAccum)
                                        {
                                            _downloadFileSizeRunningTotal += objPI._fileSize;
                                        }

                                        #endregion

                                        // submit progress report....
                                        this._bgWorkerAddFilesToImageRepository.ReportProgress(recFound,
                                            // xfer ownership of shared data...
                                            new ObjProgressInfo()
                                            {
                                                _completed =
                                                    objPI._completed
                                                ,
                                                _fileName =
                                                    objPI._fileName
                                                ,
                                                _fileSize =
                                                    objPI._fileSize
                                                ,
                                                _filesRemaining =
                                                    objPI._filesRemaining
                                                ,
                                                _recCount =
                                                    objPI._recCount
                                                ,
                                                _startup = objPI._startup
                                            });
                                    }
                                }
                            }
                            //////////////////////////////////////

                            #endregion
                        }
                        break;
                }
            } // end of foreach (KeyValuePair<SupportedDownloadFileTypes, string> kvp in fileDictionary)...

            //
            // Doing the Verify now insure 
            // that the MP3 and SRF are always on the same ISO...
            trackIndexItems = VerifyThisWillFitOnISOImage(trackIndexItems, listIndexData, listArchiveDataTableContent, path);
            if (audioFileValidated) { AddFileToImageRepository(audioFileName); }
            if (videoFileValidated) { AddFileToImageRepository(videoFileName); }
        }

        /// <summary>
        /// Veifies that the current
        /// files we are adding to the ISO
        /// can fit on the same media...
        /// </summary>
        /// <param name="trackIndexItems"></param>
        /// <param name="listIndexData"></param>
        /// <param name="listArchiveDataTableContent"></param>
        /// <param name="path"></param>
        /// <returns></returns>
        private int VerifyThisWillFitOnISOImage(int trackIndexItems
                                                , List<FileImageInfo.IndexData> listIndexData
                                                , List<FileImageInfo.ArchiveData> listArchiveDataTableContent
                                                , string path)
        {
            lock (_verifyingContentWillFitOnImage)
            {
                if (_downloadFileSizeRunningTotal > _formatFileSize)
                {
                    Log.LogWrite("VerifyThisWillFitOnISOImage()...");

                    var lastIndexDataRecord = default(FileImageInfo.IndexData);
                    var lastArchiveDataTableContentRecord = default(FileImageInfo.ArchiveData);

                    lock (_trackDownloadFileSizeAccum)
                    {
                        Log.LogWrite(string.Format("Download FileSize {0} is greater than disk capacity {1}"
                            , _downloadFileSizeRunningTotal.ToString("#,#"),
                            _formatFileSize.ToString("#,#")));
                        //
                        // The current download file size is greater than the
                        // output media file size due to the addition of the last record;
                        // this means we need to remove these records from the current archive index
                        // and add them to the index for the next output media...
                        //
                        if (listIndexData != null && listArchiveDataTableContent != null)
                        {
                            Log.LogWrite("Old Index Count: " + listIndexData.Count);
                            var index = listIndexData.Count - 1;
                            lastIndexDataRecord = listIndexData[index];
                            listIndexData.RemoveAt(index);

                            Log.LogWrite("Old DTC Count: " + listArchiveDataTableContent.Count);
                            index = listArchiveDataTableContent.Count - 1;
                            lastArchiveDataTableContentRecord = listArchiveDataTableContent[index];
                            listArchiveDataTableContent.RemoveAt(index);
                        }
                    }

                    //
                    // The support for creating multiple ISO images is both
                    // simple and not so simple at the same time but here is the story...
                    //
                    // Originally all the information that pertained to the image
                    // was captured at the beginning of the process and reused
                    // by all the phases that followed.
                    //
                    // But in order to support multiple images, these global entities
                    // will need to be updated mid-stream: The following code is
                    // the pivot point for documenting the new ISO content:
                    //
                    // 1. Need to capture the data that is stored in the ArchiveLink table.
                    //
                    lock (_objectLock)
                    {
                        if (listArchiveDataTableContent != null)
                        {
                            _dictionaryOfArchiveDataTableContent.Add(trackIndexItems,
                                new List<FileImageInfo.ArchiveData>(listArchiveDataTableContent));
                        }
                        else
                        {
                            Log.LogWrite("ListArchiveDataTableContent is null...");
                        }
                    }
                    //
                    // 2. Create a new index for the ISO image.
                    //
                    string indexName;
                    lock (_createIndexNameLock)
                    {
                        indexName = CreateIndexTextValue(trackIndexItems) + "_" + RES.Resources.RES_IndexCSVFileName;
                        CreateArchiveIndexFile(listIndexData, indexName);
                    }
                    string newIndexFile = new FileInfo(path).DirectoryName + "\\" + indexName;
                    if (File.Exists(newIndexFile))
                    {
                        AddFileToImageRepository(newIndexFile);
                        Log.LogWrite("Added new item, " + newIndexFile + ", to ImageRepository");

                        //
                        // 3. Create a new ISO image repository item
                        //
                        _imageRepositoryList.Add(new ImageRepository());
                        _imageRepository = _imageRepositoryList[Interlocked.Increment(ref _isoImageRepositoryIndex)];
                        //
                        // 4. Clear accumulators
                        //
                        lock (_trackDownloadFileSizeAccum)
                        {
                            _downloadFileSizeRunningTotal = 0;
                            Log.LogWrite("New _downloadFileSizeRunningTotal: " +
                                         _downloadFileSizeRunningTotal.ToString("#,#"));

                            if (listIndexData != null) listIndexData.Clear();
                            if (listArchiveDataTableContent != null) listArchiveDataTableContent.Clear();

                            //
                            // 5. Increment index counter
                            //
                            Interlocked.Increment(ref trackIndexItems);

                            //
                            // 6. Place records back in list...
                            //
                            if (lastIndexDataRecord != null)
                            {
                                listIndexData.Add(lastIndexDataRecord);
                                Log.LogWrite("New Index Count: " + listIndexData.Count);
                            }
                            if (lastArchiveDataTableContentRecord != null)
                            {
                                listArchiveDataTableContent.Add(lastArchiveDataTableContentRecord);
                                Log.LogWrite("New DTC Count: " + listArchiveDataTableContent.Count);
                            }
                        }
                    }
                }
                return trackIndexItems;
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="listIndexData"></param>
        /// <param name="objPI"></param>
        /// <param name="x"></param>
        private void ZeroByteFilesHandler(List<FileImageInfo.IndexData> listIndexData, ObjProgressInfo objPI, int x)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter ZeroByteFilesHandler()...");
            try
            {
                int index = 0;
                Interlocked.Exchange(ref index, x);
                var fileImageInfoIndexData = default(FileImageInfo.IndexData);

                try
                {
                    fileImageInfoIndexData = listIndexData.Find(i => i.CallID.Equals(ObjFileImageInfo.IndexFileData[index].CallID));
                }
                catch (Exception ex)
                {
                    Log.LogWrite("ZeroByteFilesHandler: " + ErrorMessageString(ex));
                    Log.LogWrite("Index: " + index);
                }

                if (null != fileImageInfoIndexData)
                {
                    if (fileImageInfoIndexData.Duration > 0)
                    {
                        // eventually add code to update...
                        try
                        {
                            Log.LogWrite(string.Format("Zero-byte file: {0} - Recording Duration: {1}", objPI._fileName, fileImageInfoIndexData.Duration));
                        }
                        catch { }
                        RecordedCalls rc = CallsArray.First(n => n.CallID.Equals(fileImageInfoIndexData.CallID));
                        if (null != rc)
                        {
                            string downLoadPath = _isoDirectoryLayout + (new FileInfo(rc.RecordingFileLocation).Name);
                            using (var awc = new ArchiveWebClient(300000)) // wait 5 minutes...
                            {
                                _autoEventZeroByteFileDownload.Reset();

                                awc.UseDefaultCredentials = true;
                                awc.DownloadFileCompleted += AwcDownloadFileCompleted;
                                awc.DownloadFileAsync(new Uri(rc.RecordingFileLink), downLoadPath, new FileInfo(rc.RecordingFileLocation).Name);

                                _autoEventZeroByteFileDownload.WaitOne();
                                objPI._fileSize = new FileInfo(downLoadPath).Length;
                                lock (_trackDownloadFileSizeAccum)
                                {
                                    _downloadFileSizeRunningTotal += objPI._fileSize;
                                }
                            }
                        }
                    }
                    else
                    {
                        Log.LogWrite(string.Format("Recording duration is 0 - valid zero-byte file: {0}", objPI._fileName));
                    }
                } // end
            }
            finally
            {
                Log.LogWrite("Exit ZeroByteFilesHandler()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// special for retrieving zero-byte files...
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        void AwcDownloadFileCompleted(object sender, AsyncCompletedEventArgs e)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter awc_DownloadFileCompleted()...");
            try
            {
                if (e.Error != null)
                {
                    Log.LogWrite(string.Format("Error downloading {0}: {1}", e.UserState, e.Error));
                }
                else if (e.Cancelled)
                {
                    Log.LogWrite(string.Format("Download of {0} cancelled.", e.UserState));
                }
                else
                {
                    Log.LogWrite(string.Format("Successfully downloaded {0}", e.UserState));
                }
            }
            catch { }
            finally
            {
                Log.LogWrite("Exit awc_DownloadFileCompleted()... " + FormatElapsedTime(stopwatch));
                _autoEventZeroByteFileDownload.Set();
            }
        }

        /// <summary>
        /// add file to image repository object
        /// </summary>
        /// <param name="path"></param>
        private void AddFileToImageRepository(string path)
        {
            _imageRepository.AddNewFile(path);
        }

        /// <summary>
        /// add folder to image repository object
        /// </summary>
        /// <param name="path"></param>
        private void AddFolderToImageRepository(string path)
        {
            _imageRepository.AddNewFolder(path);
        }

        #endregion

        ////[ End Phase 2 - Populate ISO Image Repository ]///////////////////////
        #endregion



        #region Phase 3 - Create ISO Images...
        //////////////////////////////////////////////////////////////////////////
        #region Background Worker Who Creates ISO Images...

        /// <summary>
        /// performs ISO creation work on a background thread
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void BgWorkerISOWriterDoWork(object sender, DoWorkEventArgs e)
        {
            Log.LogWrite("1. WAITFOR-PHASE-3 ProcessImageRepositoryObject(): _autoEventIsoWriterCriticalLoop.WaitOne - hold XXXXXXXXXX");
            _autoEventIsoWriterCriticalLoop.WaitOne();
            Log.LogWrite("2. START-PHASE-3a BgWorkerISOWriterDoWork(): _autoEventIsoWriterCriticalLoop.WaitOne - released XXXXXXXXXX");

            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter BgWorkerISOWriterDoWork()...");

            _autoEventCdBuilderIsoCreationInProgress.Reset();
            _autoEventIsoWriterWorking.Reset();

            _elapsedIsoCreationTime.Reset();
            _elapsedIsoCreationTime.Start();

            _msgs = string.Format("Begin ISO Writer - repository item count: {0}",
                _imageRepository.Items.Count.ToString(CultureInfo.InvariantCulture));
            UpdateEventViewer(_msgs);

            if (_imageRepository.Items.Count < 1)
            {
                e.Result = null;
                return;
            }
            try
            {
                _bgWorkerISOWriter.ReportProgress(0);

                var builder = new CDBuilder
                {
                    VolumeIdentifier = _mediaVolumeName
                };
                lock (_createIndexNameLock)
                {
                    var files = _imageRepository.Items.ToList();
                    var isoDirectoryStructure = _isoDirectoryLayout.Substring(_isoDirectoryLayout.IndexOf(':') + 2);
                    foreach (var file in files)
                    {
                        var dir = isoDirectoryStructure;
                        builder.AddDirectory(dir);
                        builder.AddFile(dir + "\\" + file.Name, file.FullName);
                    }
                }
                Action action = () => CdBuilderStartIsoCreationProcess(builder);
                AsyncCallback callback = CdBuilderIsoCreationProcessCompleted;
                action.BeginInvoke(callback, action);
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                UpdateEventViewer(_msgs, EventLogEntryType.Error);
                e.Result = null;
            }
            finally
            {
                _autoEventCdBuilderIsoCreationInProgress.WaitOne();
                e.Cancel = _bgWorkerISOWriter.CancellationPending;
                Log.LogWrite("Exit BgWorkerISOWriterDoWork()... " + FormatElapsedTime(stopwatch));
                _autoEventIsoWriterWorking.Set();
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="builder"></param>
        /// <returns></returns>
        private void CdBuilderStartIsoCreationProcess(CDBuilder builder)
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter CdBuilderStartIsoCreationProcess(...)...");
            try
            {
                lock (_createIndexNameLock)
                {
                    if (builder != null) builder.Build(_outputLocation);
                }
            }
            finally
            {
                Log.LogWrite("Exit CdBuilderStartIsoCreationProcess(...)... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        private void CdBuilderStartIsoCreationProcess()
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter CdBuilderStartIsoCreationProcess()...");
            try
            {
                lock (_createIndexNameLock)
                {
                    var builder = new CDBuilder
                    {
                        VolumeIdentifier = _mediaVolumeName
                    };
                    var files = _imageRepository.Items.ToList();
                    files.ForEach(f => builder.AddFile(f.Name, f.FullName));
                    builder.Build(_outputLocation);
                }
            }
            finally
            {
                Log.LogWrite("Exit CdBuilderStartIsoCreationProcess()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="ar"></param>
        private void CdBuilderIsoCreationProcessCompleted(IAsyncResult ar)
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter CdBuilderIsoCreationProcessCompleted()...");
            try
            {
                // fetch the delegate by casting the AsyncState.
                var action = ar.AsyncState as Action;

                Log.LogWrite(string.Format("1. AR State: {0} --- Done? {1}", ar.AsyncState, ar.IsCompleted));
                if (action != null)
                {
                    Log.LogWrite(string.Format("Action ok {0}", action));
                    action.EndInvoke(ar);
                }
                Log.LogWrite(string.Format("2. AR State: {0} --- Done? {1}", ar.AsyncState, ar.IsCompleted));

                _msgs = "CdBuilderIsoCreationProcessCompleted processing completed successfully...";
                Log.LogWrite(_msgs);
            }
            finally
            {
                Log.LogWrite("Exit CdBuilderIsoCreationProcessCompleted()... " + FormatElapsedTime(stopwatch));
                _autoEventCdBuilderIsoCreationInProgress.Set();
                //_autoEventIsoWriterWorking.Set();
            }
        }

        /// <summary>
        /// show progress while synchronous CDBuilder
        /// is creating the ISO image...
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        void BgWorkerISOWriterProgressChanged(object sender, ProgressChangedEventArgs e)
        {
            try
            {
                btnCreateOutputFile.Enabled = false;
                toolStripProgressBar.Style = ProgressBarStyle.Marquee;

                lock (_createIndexNameLock)
                {
                    var completedTasks = _isoIterateImageRepository;
                    if (completedTasks > 0)
                    {
                        var totalTasks = _imageRepositoryList.Count;
                        var percentageDone = (int)(((double)completedTasks / totalTasks) * 100);

                        _msgs =
                            string.Format(
                                Resources.SRIPArchiveClientForm_BgWorkerISOWriterProgressChanged_Image_File_Count_
                                , totalTasks
                                , (totalTasks - completedTasks)
                                , (percentageDone)
                                , TimeRemainingEstimate(totalTasks, completedTasks, _elapsedIsoCreationTime));

                        toolStripStatusLabel.Text = _msgs;
                        Log.LogWrite("$*$*$*$ " + _msgs + " $*$*$*$");
                    }
                    PopulateStatusTextBox(Resources.SRIPArchiveClientForm_BgWorkerISOWriterProgressChanged_ISO_Image_Creation_In_Progress_, true);

                }
            }
            catch (Exception ex) { Log.LogWrite("Progress warning: " + ex.Message); }
        }

        /// <summary>
        /// Respond to ISO write completion
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void BgWorkerISOWriterRunWorkerCompleted(object sender, RunWorkerCompletedEventArgs e)
        {
            btnCreateOutputFile.Enabled = true;
            //
            // wait for data to be downloaded...
            //
            Log.LogWrite("1. ENDING-PHASE-3a BgWorkerISOWriterDoWork(): _autoEventIsoWriterWorking.WaitOne - hold XXXXXXXXXX");
            _autoEventIsoWriterWorking.WaitOne();
            Log.LogWrite("2. END-PHASE-3a BgWorkerISOWriterDoWork(): _autoEventIsoWriterWorking.WaitOne - released XXXXXXXXXX");

            Cursor.Current = Cursors.Default;
            var stopwatch = new Stopwatch(); stopwatch.Start();
            try
            {
                Log.LogWrite("Enter _bgWorkerISOWriter_RunWorkerCompleted...");

                if (e.Cancelled || _cancellationISOWriter)
                {
                    _isoImageRepositoryIndex = 0;
                }
                _bgWorkerISOWriter.DoWork -= BgWorkerISOWriterDoWork;
                _bgWorkerISOWriter.ProgressChanged -= BgWorkerISOWriterProgressChanged;
                _bgWorkerISOWriter.RunWorkerCompleted -= BgWorkerISOWriterRunWorkerCompleted;
                _timeRemainingEstimates.Stop();
                WrapUpCompletedEvent(e);

                try
                {
                    if (_isoImageRepositoryIndex > 0)
                    {
                        Interlocked.Decrement(ref _isoImageRepositoryIndex);   // begin clearing
                        Interlocked.Increment(ref _isoIterateImageRepository);
                        _imageRepository = _imageRepositoryList[_isoIterateImageRepository];

                        lock (_createIndexNameLock)
                        {
                            //
                            // fix txtUserName to handle occasions where
                            // the user name is a domain name...
                            //
                            var fixedTxtUserName = txtUserName.Text.Replace("\\", "_");

                            txtOutputLocation.Text =
                                CreateISOImageOutputFileName(new FileInfo(txtOutputLocation.Text)
                                                                 .DirectoryName + "\\" + fixedTxtUserName + "_",
                                    CreateIndexTextValue(_isoIterateImageRepository),
                                    false);
                        }
                        //
                        // Wiederholen Sie diesen!...
                        //
                        _timeRemainingEstimates.Reset(); _timeRemainingEstimates.Start();
                        ProcessImageRepositoryObject();
                    }
                }
                catch (Exception ex)
                {
                    UpdateEventViewer(string.Format("Error in BgWorkerISOWriterRunWorkerCompleted(): {0}", ex.Message));
                }
            }
            finally
            {
                Log.LogWrite("Exit BgWorkerISOWriterRunWorkerCompleted... " + FormatElapsedTime(stopwatch));
            }
        }

        //////////////////////////////////////////////////////////////////////////

        #region ISO Writer Calls When Completed

        /// <summary>
        /// 
        /// </summary>
        /// <param name="e"></param>
        private void WrapUpCompletedEvent(RunWorkerCompletedEventArgs e)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter WrapUpCompletedEvent()...");

            using (var frm = e.Result != null ? e.Result as ISOFormatter : null)
            {
                bool wrapUpSuccessful = true;
                try
                {
                    if (e.Cancelled)
                    {
                        wrapUpSuccessful = false;
                        string step = RES.Resources.RES_Authenticating;
                        if (txtBoxStatus.Text.LastIndexOf(RES.Resources.RES_Formatting, StringComparison.Ordinal) > 0)
                        {
                            step = RES.Resources.RES_Formatting;
                        }
                        else if (txtBoxStatus.Text.LastIndexOf(RES.Resources.RES_Adding, StringComparison.Ordinal) > 0)
                        {
                            step = RES.Resources.RES_Adding;
                        }

                        _msgs = string.Format(RES.Resources.RES_CanceledWhileThisRecording
                            , txtBoxStatus.Text.Split('\\')[txtBoxStatus.Text.Split('\\').Length - 1], step);
                        PopulateStatusTextBox(_msgs, true);
                        UpdateEventViewer(_msgs);
                        File.Delete(txtOutputLocation.Text);
                    }
                    else
                    {
                        if (e.Error != null)
                        {
                            wrapUpSuccessful = false;
                            if (!_cancelledCOMRunTimeError)
                            {
                                _msgs = string.Format(RES.Resources.RES_ErrorFileSizeBytes
                                    , e.Error.Message
                                    , _imageRepository.CurrentFileProcessing
                                    , _imageRepository.CurrentFileProcessingFileSize);
                            }
                            try
                            {
                                File.Delete(txtOutputLocation.Text);
                            }
                            catch (Exception ex)
                            {
                                _msgs = ErrorMessageString(ex);
                                Log.LogWrite(_msgs);
                            }
                            PopulateStatusTextBox(_msgs, true);
                            UpdateEventViewer(_msgs);
                        }
                        else
                        {
                            if (_imageRepository.Items.Count > 0)
                            {
                                // do we have another ISO to process...
                                string fileName = null;
                                try
                                {
                                    fileName = Path.GetFileName(txtOutputLocation.Text);
                                }
                                catch (Exception ex)
                                {
                                    _msgs = string.Format("File not found: " + txtOutputLocation.Text);
                                    Log.LogWrite(_msgs);
                                    Log.LogWrite(ErrorMessageString(ex));
                                }

                                if (fileName != null && File.Exists(txtOutputLocation.Text))
                                {
                                    _msgs = string.Format(RES.Resources.RES_CreatedFileSizeBytesElapsedTime
                                        , FormatElapsedTime(_elapsedIsoCreationTime)
                                        , fileName.ToUpper()
                                        , new FileInfo(txtOutputLocation.Text).Length.ToString("#,#")
                                        , _imageRepository.Items.Count - 1); // don't count the index file
                                }
                                else
                                {
                                    wrapUpSuccessful = false;
                                    _msgs = string.Format("File not found: " + txtOutputLocation.Text);
                                    Log.LogWrite(_msgs);
                                }
                                PopulateStatusTextBox(_msgs, true);
                                UpdateEventViewer(_msgs);
                            }
                        }
                    }

                    if (wrapUpSuccessful && !e.Cancelled && e.Error == null && (_imageRepository.Items.Count > 0))
                    {
                        //frm = e.Result as ISOFormatter;
                        if (_doNotUpdateArchiveDbTables.Equals(false))
                            UpdateTables();
                        UpdateConfigSettings();
                        RemoveImageRepositoryObject(frm);
                    }
                }
                finally
                {
                    if (_isoImageRepositoryIndex <= 0)
                        //RestoreUI(frm);
                        RestoreUI(wrapUpSuccessful);
                    Log.LogWrite("Exit WrapUpCompletedEvent()... " + FormatElapsedTime(stopwatch));
                }
            }
            //// using before me
        }

        #endregion

        ////[ End Background Worker Who Creates ISO Images ]/////////////////////
        #endregion

        #region Support Writing ISO Image...

        /// <summary>
        /// setup ISO "hardware"
        /// </summary>
        /// <returns></returns>
        private void InitRepository()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter InitRepository()...");

            Application.DoEvents();
            // Downstream adjustment = get an image repository item from the list
            _imageRepository = _imageRepositoryList[_isoIterateImageRepository];
            var ifsi = _imageRepository as IFileSystemImage;

            // make sure it has data
            if (_imageRepository.Items.Count < 1) return;

            var fstype = FsiFileSystems.FsiFileSystemNone;
            fstype |= FsiFileSystems.FsiFileSystemISO9660;
            fstype |= FsiFileSystems.FsiFileSystemJoliet;
            ifsi.FileSystemsToCreate = fstype;
            ifsi.VolumeName = txtMediaVolumeName.Text;

            // Another downstream adjustment - update content that will be sent to database
            ObjFileImageInfo.ArchiveFileName = _outputLocation;
            ObjFileImageInfo.ItemCount = _imageRepository.Items.Count - 1;
            ObjFileImageInfo.ArchiveTableList = _dictionaryOfArchiveDataTableContent[_isoIterateImageRepository];
            //
            // back to normal from here...

            // default type
            ifsi.ChooseImageDefaultsForMediaType(IMAPI_MEDIA_PHYSICAL_TYPE.IMAPI_MEDIA_TYPE_DISK);

            Stop += _imageRepository.CancelOp;
            try
            {
                if (ObjFileImageInfo.UseObjectDates)
                {
                    // because we allow the server to select the items
                    // by date range, this will normally not be true...
                    //
                    _imageRepository.StartDateRange = ObjFileImageInfo.StartDateRange;  //new DateTime(1990, 1, 1);
                    _imageRepository.EndDateRange = ObjFileImageInfo.EndDateRange;       //DateTime.Now;
                }

                _imageRepository.Update += AsyncRepositoryUpdate;
                Cursor = Cursors.WaitCursor;
                _msgs = string.Format(RES.Resources.RES_CalculatingSizeFor, txtOutputLocation.Text);
                PopulateStatusTextBox(_msgs, true);
                Application.DoEvents();

                var calculateImageSizeTimer = new Stopwatch();
                calculateImageSizeTimer.Start();

                try
                {
                    toolStripProgressBar.Style = ProgressBarStyle.Marquee;
                    _imageRepository.CalculateSizeBeforeFormatting();
                    //
                    // insure FileSystemsToCreate is set correctly: 
                    // 8.5GB (9,126,805,504 bytes) - UDF 
                    // 4.7GB (5,046,586,572 bytes) - ISO9660, Joliet, UDF
                    //
                    if (_imageRepository.SizeBeforeFormatting > _maxJolietFormatFileSize || _udfFileSystemRequired)
                    {
                        ifsi.FileSystemsToCreate = FsiFileSystems.FsiFileSystemUDF;
                    }

                    //
                    // insure size doesn't exceed UDF max size: 
                    // 8.5GB (9,126,805,504 bytes) - UDF                     
                    //
                    if (_imageRepository.SizeBeforeFormatting > _maxUDFFormatFileSize)
                    {
                        _msgs = string.Format("Warning: Image size {0} bytes exceeds max size {1}..."
                            , _imageRepository.SizeBeforeFormatting.ToString("#,#")
                            , _maxUDFFormatFileSize.ToString("#,#"));

                        PopulateStatusTextBox(_msgs, true);
                        UpdateEventViewer(_msgs);
                    }
                    //
                    // need to verify TEMP folder has at *least* twice 
                    // the amount of free space as the size of 
                    // _imageRepository.SizeBeforeFormatting available 
                    // since ISO creation writes file to TEMP first then 
                    // streams the formatted results into the ISO image
                    //
                    var sDevice = string.Format("win32_logicaldisk.deviceid=\"{0}:\""
                        , Path.GetTempPath().Split(':')[0]);
                    VerifyTempFolderFreeSpaceAcceptableForSelectedFileImage(sDevice);
                }
                finally
                {
                    toolStripProgressBar.Style = ProgressBarStyle.Continuous;
                }

                calculateImageSizeTimer.Stop();
                _msgs = string.Format(RES.Resources.RES_CalculatedTotalInputFileSize, FormatElapsedTime(calculateImageSizeTimer), _imageRepository.SizeBeforeFormatting.ToString("#,#"));
                PopulateStatusTextBox(_msgs, true);
                UpdateEventViewer(_msgs);
            }
            finally
            {
                ifsi = null;
                this.Cursor = Cursors.Arrow;
                Log.LogWrite("Exit InitRepository()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// Runs process in background thread
        /// </summary>
        private void RunISOWriterProcessor()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter RunISOWriterProcessor()...");

            try
            {
                btnCreateOutputFile.Enabled = true;
                _bgWorkerISOWriter.WorkerReportsProgress = true;
                _bgWorkerISOWriter.DoWork += BgWorkerISOWriterDoWork;
                _bgWorkerISOWriter.ProgressChanged += BgWorkerISOWriterProgressChanged;
                _bgWorkerISOWriter.RunWorkerCompleted += BgWorkerISOWriterRunWorkerCompleted;
                _bgWorkerISOWriter.RunWorkerAsync(txtOutputLocation.Text);
            }
            finally
            {
                Log.LogWrite("Exit RunISOWriterProcessor()... " + FormatElapsedTime(stopwatch)); 
            }
        }

        #endregion

        ////[ End Phase 3 - Create ISO Images ]//////////////////////////////////
        #endregion



        #region Event Handlers...

        //////////////////////////////////////////////////////////////////////////

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtUserName_Validated(object sender, EventArgs e)
        {
            Control ctrl = (Control)sender;
            if (txtUserName.Text.Length.Equals(0)) _errProvider.SetError(ctrl
                , Resources.RES_UserNameNotProvided);
            else _errProvider.SetError(ctrl, "");
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtPassword_Validated(object sender, EventArgs e)
        {
            Control ctrl = (Control)sender;
            if (txtPassword.Text.Length.Equals(0)) _errProvider.SetError(ctrl
                , Resources.RES_PasswordNotProvided);
            else _errProvider.SetError(ctrl, "");
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void dtpStartDate_Validated(object sender, EventArgs e)
        {
            Control sdCtrl = dtpStartDate as Control;
            Control stCtrl = dtpStartTime as Control;
            DateTime sd = SetDate(dtpStartDate, dtpStartTime);
            DateTime ed = SetDate(dtpEndDate, dtpEndTime);
            bool ok = true;
            if (sd.Ticks > ed.Ticks)
            {
                if (dtpStartDate.Value > dtpEndDate.Value)
                    _errProvider.SetError(sdCtrl
                        , RES.Resources.RES_StartDateGreaterThanEndDate);
                else
                    _errProvider.SetError(stCtrl
                        , RES.Resources.RES_StartTimeGreaterThanEndTime);

                ok = false;
            }

            if (ok && (dtpEndDate.Value.Subtract(dtpStartDate.Value).Days > _archiveNumberOfDaysLimit))
            {
                var over = dtpEndDate.Value.Subtract(dtpStartDate.Value).Days - (_archiveNumberOfDaysLimit);
                var validStartDate = dtpStartDate.Value.AddDays(over);
                _errProvider.SetError(sdCtrl,
                    string.Format(Resources.RES_Search_Date_Range_Greater_Than_Max, _archiveNumberOfDaysLimit,
                        validStartDate));

                ok = false;
            }

            if (ok)
            {
                _errProvider.SetError(sdCtrl, "");
                _errProvider.SetError(stCtrl, "");
            }

        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void dtpStartTime_Validated(object sender, EventArgs e)
        {
            dtpStartDate_Validated(this, e);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void dtpEndDate_Validated(object sender, EventArgs e)
        {
            dtpStartDate_Validated(this, e);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void dtpEndTime_Validated(object sender, EventArgs e)
        {
            dtpStartDate_Validated(this, e);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtOutputLocation_Validated(object sender, EventArgs e)
        {
            Control ctrl = (Control)sender;
            if (txtOutputLocation.Text.Length.Equals(0)) _errProvider.SetError(ctrl
                , RES.Resources.RES_OutputLocationNotProvided);
            else _errProvider.SetError(ctrl, "");
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtMediaVolumeName_Validated(object sender, EventArgs e)
        {
            Control ctrl = (Control)sender;
            if (txtMediaVolumeName.Text.Length.Equals(0)) _errProvider.SetError(ctrl
                , RES.Resources.RES_OutputVolumeLabelNotProvided);
            else
            {
                if (txtMediaVolumeName.Text.Length.Equals(txtMediaVolumeName.MaxLength + 1)) _errProvider.SetError(ctrl
                  , RES.Resources.RES_OutputVolumeLabelExceedsMaxLength);
                else
                    _errProvider.SetError(ctrl, "");
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtWebServiceURL_Validated(object sender, EventArgs e)
        {
            Control ctrl = (Control)sender;
            if (txtWebServiceURL.Text.Length.Equals(0)) _errProvider.SetError(ctrl
                , RES.Resources.RES_WebServiceURLNotProvided);
            else _errProvider.SetError(ctrl, "");
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtISODirectoryLayout_Validated(object sender, EventArgs e)
        {
            Control ctrl = (Control)sender;
            if (txtISODirectoryLayout.Text.Length.Equals(0))
                _errProvider.SetError(ctrl, Resources.RES_ISODirectoryLayoutNotProvided);
            else
            {
                _errProvider.SetError(ctrl,UserDirectoryLocalDirectoryMisMatch(txtISODirectoryLayout.Text)
                        ? Resources.SRIPArchiveClientForm_ValidateConfigPage_ISO_Directory_Given_Is_Not_Valid_Path_
                        : "");
            }
        }

        private void txtISOFileReaderOutputDir_Validated(object sender, EventArgs e)
        {
            Control ctrl = (Control)sender;
            if (txtISOFileReaderOutputDir.Text.Length.Equals(0))
                _errProvider.SetError(ctrl, Resources.SRIPArchiveClientForm_txtISOFileReaderOutputDir_Validated_An_Output_Directory_For_Viewer_Was_Not_Provided_);
            else
            {
                _errProvider.SetError(ctrl, UserDirectoryLocalDirectoryMisMatch(txtISODirectoryLayout.Text)
                        ? Resources.SRIPArchiveClientForm_ValidateConfigPage_ISO_Directory_Given_Is_Not_Valid_Path_
                        : "");
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void chkBoxIncludeArchivedCalls_CheckedChanged(object sender, EventArgs e)
        {
            _includeArchivedCalls = chkBoxIncludeArchivedCalls.Checked;
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void radioBtnOther_CheckedChanged(object sender, EventArgs e)
        {
            if (radioBtnOther.Checked)
            {
                _udfFileSystemRequired = true;
                _formatFileSize = _maxUDFFormatFileSize;
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void radioBtnDVD_CheckedChanged(object sender, EventArgs e)
        {
            if (radioBtnDVD.Checked)
            {
                _udfFileSystemRequired = false;
                _formatFileSize = _maxDVDFormatFileSize;
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void radioBtnCD_CheckedChanged(object sender, EventArgs e)
        {
            if (radioBtnCD.Checked)
            {
                _udfFileSystemRequired = false;
                _formatFileSize = _maxCDFormatFileSize;
            }
        }
        /// <summary>
        /// support making selections from
        /// ISO input location auto-complete list...
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtISOFile_KeyUp(object sender, KeyEventArgs e)
        {
            if (e.KeyValue.Equals(13))
            {
                if (btnISOFileLoad.Enabled)
                {
                    btnISOFileLoad_Click(this, null);
                }
            }
        }
        /// <summary>
        /// handler for NumericUpDown control
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void nudMultiFileDownload_ValueChanged(object sender, EventArgs e)
        {
            _maxNumberOfFilesToDownloadConcurrently = int.Parse(nudMultiFileDownload.Value.ToString());
            //
            // Automatically set the connections count to files * 3 or cap at 12
            // Apparently, as .NET pools TCP connections, they deliberately limit apps to 
            // 2 active connections (I assume per process) .  Microsoft recommends 
            // setting this to 12 times the number of CPUs
            if (12 < (_maxNumberOfFilesToDownloadConcurrently * 3))
                nudConnections.Value = 12;
            else
                nudConnections.Value = _maxNumberOfFilesToDownloadConcurrently * 3;

            Log.LogWrite("Max number of files to download concurrently: " + _maxNumberOfFilesToDownloadConcurrently);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void nudNumberOfCPUs_ValueChanged(object sender, EventArgs e)
        {
            _numberOfCPUs = int.Parse(nudNumberOfCPUs.Value.ToString());

            Log.LogWrite("Number of CPU's: " + _numberOfCPUs);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void nudConnections_ValueChanged(object sender, EventArgs e)
        {
            _numberOfCPUConnections = int.Parse(nudConnections.Value.ToString());

            Log.LogWrite("Number of CPU connections: " + _numberOfCPUConnections);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void chkBoxDoNotDeleteDownloadedFiles_CheckedChanged(object sender, EventArgs e)
        {
            _doNotDeleteDownloadedFiles = chkBoxDoNotDeleteDownloadedFiles.Checked;
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void chkBoxDoNotDownloadVideoFiles_CheckedChanged(object sender, EventArgs e)
        {
            _doNotDownloadVideoFiles = chkBoxDoNotDownloadVideoFiles.Checked;
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void chkBoxUpdateArchiveTables_CheckedChanged(object sender, EventArgs e)
        {
            _doNotUpdateArchiveDbTables = chkBoxDoNotUpdateArchiveTables.Checked;
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void chkBoxCreateISOImage_CheckedChanged(object sender, EventArgs e)
        {
            _doNotCreateISOImage = chkBoxDoNotCreateISOImage.Checked;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void comboBoxTimeZoneList_SelectedIndexChanged(object sender, EventArgs e)
        {
            _currentTimeZoneSelected = comboBoxTimeZoneList.SelectedItem.ToString(); // cross thread access...

            // when the list changes and the viewer is populated, the
            // new tz needs to be applied to the datetime in the viewer...
            if (btnISOFileLoad.Enabled)
            {
                SelectAllItemsInViewerGrid();
            }
        }
        /// <summary>
        /// adding search to grid
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void toolStripTextBoxFilter_TextChanged(object sender, EventArgs e)
        {
            var dv = _bindingSource.List as DataView;

            if (dv != null)
            {
                var filterOnStuff = SearchFieldData[toolStripComboBoxColumnNames.SelectedIndex].DataPropertyName;
                var thisStuff = toolStripTextBoxFilter.Text;
                dv.RowFilter = filterOnStuff + " like '%" + thisStuff + "%'";
            }

            if (_selectAllRows)
                _nrOfRowsSelected = _dgISOContentView.Rows.Count - 1;

            btnSelectAll.Enabled = _dgISOContentView.Rows.Count > 1;
        }

        /// <summary>
        /// support drag'n'drop on grid surface
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void _dgISOContentView_DragDrop(object sender, DragEventArgs e)
        {
            var arr = (Array)e.Data.GetData(DataFormats.FileDrop);
            if (arr != null && arr.Length > 0)
            {
                var path = arr.GetValue(0) as string;
                txtISOFile.Text = path;

                if (btnISOFileLoad.Enabled)
                {
                    btnISOFileLoad_Click(this, null);
                }
            }
        }
        /// <summary>
        /// support drag'n'drop on grid surface
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void _dgISOContentView_DragEnter(object sender, DragEventArgs e)
        {
            e.Effect = e.Data.GetDataPresent(DataFormats.FileDrop) && ValidISOContentViewerFile(e)
                ? DragDropEffects.Copy
                : DragDropEffects.None;
        }
        /// <summary>
        /// toggle the select check box for all
        /// items in the viewer
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void btnSelectAll_Click(object sender, EventArgs e)
        {
            string text = btnSelectAll.Text;
            if (text.Equals(_strSelectAll))
            {
                btnSelectAll.Text = _strSelectNone;
                _selectAllRows = true;
            }
            else
            {
                btnSelectAll.Text = _strSelectAll;
                _selectAllRows = false;
            }

            SelectAllItemsInViewerGrid();
            _dgISOContentView.RefreshEdit();

        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void tabControlISOWriter_SelectedIndexChanged(object sender, EventArgs e)
        {
            int index = (sender as TabControl).SelectedIndex;
            string tabName = (sender as TabControl).SelectedTab.Text;

            if ((tabName.Equals(RES.Resources.RES_TAB_Viewer) || (index == 2)) && (grpBoxIndexContents.Enabled))
            {
                btnSelectAll.Visible = true;
                btnSelectAll.Enabled =
                btnCreateOutputFile.Enabled = (_dgISOContentView.Rows.Count > 1);
                btnCreateOutputFile.Text = RES.Resources.RES_BTN_Restore;
            }
            else
            {
                btnCreateOutputFile.Enabled = true;
                if (grpBoxIndexContents.Enabled)
                    btnCreateOutputFile.Text = RES.Resources.RES_BTN_Create;
                else
                    btnCreateOutputFile.Text = RES.Resources.RES_BTN_Cancel;

                btnSelectAll.Visible = false;
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtISOFile_TextChanged(object sender, EventArgs e)
        {
            btnISOFileLoad.Enabled = (
                (txtISOFile.Text.Length > 0
                && (txtISOFile.Text.Contains(".iso") ||
                    (txtISOFile.Text.Contains(RES.Resources.RES_IndexCSVFileName))))
                &&
                (txtISOFileReaderOutputDir.Text.Length > 0));

            btnSelectAll.Enabled = _dgISOContentView.Rows.Count > 1;
            _isoReaderInputFile = txtISOFile.Text; // cross thread access...
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void btnISOFileBrowse_Click(object sender, EventArgs e)
        {
            _ofDlg.Filter = "ISO Files|*.iso|Index Files|*index.csv";
            if (_ofDlg.ShowDialog(this) == DialogResult.OK)
            {
                _isoReaderInputFile = txtISOFile.Text = _ofDlg.FileName;
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void btnISOFileLoad_Click(object sender, EventArgs e)
        {
            try
            {
                btnSelectAll.Text = _strSelectAll;
                _selectAllRows = false;

                // get data...
                SelectAllItemsInViewerGrid();

                btnSelectAll.Enabled =
                btnCreateOutputFile.Enabled = (_dgISOContentView.Rows.Count > 1);

                //if (btnCreateOutputFile.Enabled)
                //    toolStripTextBoxFilter.Enabled = true;
                //else
                //    toolStripTextBoxFilter.Enabled = false;

                toolStripTextBoxFilter.Enabled = true;

                //Bug #3602: show vol name on viewer page
                grpBoxIndexContents.Text = RES.Resources.RES_ContentsFor + _contentsForVolumeName;
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                UpdateEventViewer(_msgs, EventLogEntryType.Error);
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtISOFileReaderOutputDir_TextChanged(object sender, EventArgs e)
        {
            btnISOFileLoad.Enabled = (
                 (txtISOFile.Text.Length > 0
                 && (txtISOFile.Text.Contains(".iso") ||
                     (txtISOFile.Text.Contains(RES.Resources.RES_IndexCSVFileName))))
                 &&
                 (txtISOFileReaderOutputDir.Text.Length > 0));

            btnSelectAll.Enabled = _dgISOContentView.Rows.Count > 1;
            _isoReaderOutputLocation = txtISOFileReaderOutputDir.Text; // cross thread access...
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void btnISOReaderOutputDir_Click(object sender, EventArgs e)
        {
            if (_fbDlg.ShowDialog(this) == DialogResult.OK)
            {
                txtISOFileReaderOutputDir.Text = _fbDlg.SelectedPath;
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void btnCopyText_Click(object sender, EventArgs e)
        {
            if (txtBoxStatus.Text.Length > 0)
            {
                if (txtBoxStatus.SelectionLength < 1)
                    // select the text...
                    txtBoxStatus.SelectAll();

                // copy to clipboard...
                txtBoxStatus.Copy();

                // reset...
                txtBoxStatus.SelectionLength = 0;

                MessageBox.Show(this
                    , RES.Resources.RES_StatusContentCopied
                    , ""
                    , MessageBoxButtons.OK
                    , MessageBoxIcon.Information);
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void _dgISOContentView_ColumnHeaderMouseClick(object sender, DataGridViewCellMouseEventArgs e)
        {
            #region Select all here...
            if (btnSelectAll.Enabled)
            {
                if (e.ColumnIndex == 0)
                {
                    _selectAllRows = !_selectAllRows;
                    SelectAllItemsInViewerGrid();
                    if (_selectAllRows)
                    {
                        _nrOfRowsSelected = _dgISOContentView.RowCount - 1;
                        btnSelectAll.Text = _strSelectNone;
                    }
                    else
                    {
                        _nrOfRowsSelected = 0;
                        btnSelectAll.Text = _strSelectAll;
                    }
                    _dgISOContentView.RefreshEdit();
                }
            }
            #endregion
        }
        /// <summary>
        /// allow us to toggle checkbox
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void _dgISOContentView_CellContentClick(object sender, DataGridViewCellEventArgs e)
        {
            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter _dgISOContentView_CellContentClick()...");
            try
            {
                if (e.RowIndex < 0) return;

                if (_dgISOContentView.Columns[e.ColumnIndex].GetType() == typeof(DataGridViewCheckBoxColumn))
                {
                    var formattedValue = _dgISOContentView[e.ColumnIndex, e.RowIndex].FormattedValue;
                    var select = formattedValue != null && !bool.Parse(formattedValue.ToString());

                    _dgISOContentView[e.ColumnIndex, e.RowIndex].Value = select;

                    if (select) Interlocked.Increment(ref _nrOfRowsSelected);
                    else Interlocked.Decrement(ref _nrOfRowsSelected);

                    if (_nrOfRowsSelected.Equals(0)) btnSelectAll.Text = _strSelectAll;
                    else btnSelectAll.Text = _strSelectNone;
                }
            }
            catch (Exception ex)
            {
                Log.LogWrite("Error during cell content click...");
                _msgs = ErrorMessageString(ex);
                Log.LogWrite(_msgs);
            }
            finally
            {
                Log.LogWrite("Exit _dgISOContentView_CellContentClick()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// double click to play a recording...
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void _dgISOContentView_CellContentDoubleClick(object sender, DataGridViewCellEventArgs e)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter _dgISOContentView_CellContentDoubleClick()...");
            try
            {
                if (e.RowIndex < 0) return;

                if (_dgISOContentView.Columns[e.ColumnIndex].GetType() == typeof(DataGridViewLinkColumn))
                {
                    // we need to get the file and load it in the output folder...
                    Log.LogWrite("Extract the audio/video file from ISO...");
                    var fileWeNeed = _dgISOContentView[e.ColumnIndex, e.RowIndex].Value.ToString();
                    var playThisFile = LoadISOContentToLocal(fileWeNeed);

                    if (!string.IsNullOrEmpty(playThisFile))
                    {
                        string ext = new FileInfo(playThisFile).Extension.ToUpper().Substring(1);
                        switch ((SupportedDownloadFileTypes)Enum.Parse(typeof(SupportedDownloadFileTypes), ext))
                        {
                            case SupportedDownloadFileTypes.MP3:
                                Log.LogWrite("Play this audio file: " + playThisFile);
                                Process.Start(playThisFile);
                                break;
                            case SupportedDownloadFileTypes.SRF:
                                {
                                    int progressBarDefaultStep = toolStripProgressBar.Step;
                                    string saveToolStripStatusText = toolStripStatusLabel.Text;
                                    try
                                    {
                                        Log.LogWrite("Step 1. Init video setup...");
                                        Cursor.Current = Cursors.WaitCursor;
                                        toolStripProgressBar.Visible = true;
                                        toolStripProgressBar.Style = ProgressBarStyle.Continuous;
                                        toolStripProgressBar.Step = 25;
                                        toolStripStatusLabel.Text = string.Format(RES.Resources.RES_OpeningAudioVideoFile);
                                        Application.DoEvents();

                                        bool safeToPlay = true;
                                        string movie = playThisFile.ToUpper().Replace(".SRF", ".MOV");
                                        Log.LogWrite("Prepare to process or reuse this video file: " + movie);

                                        if (!File.Exists(movie))
                                        {
                                            Log.LogWrite("Step 2. Create the movie file...");
                                            var mm = new MovMaker(movie, new ProgressBar());
                                            toolStripProgressBar.PerformStep(); // 1
                                            Application.DoEvents();

                                            Log.LogWrite("Step 2 Results: success...");
                                            Log.LogWrite("Step 3. Create movie file from: " + playThisFile);
                                            safeToPlay = mm.MakeMovie(playThisFile
                                                , 0
                                                , new[] { "" }
                                                , new long[] { 0 }
                                                , new long[] { 0 });

                                            Log.LogWrite(safeToPlay
                                                             ? "Step 3 Results: success..."
                                                             : "Step 3 Results: failure...");
                                            toolStripProgressBar.PerformStep(); //2
                                            Application.DoEvents();
                                        }
                                        else
                                        {
                                            Log.LogWrite("This movie file has been downloaded previously and will be reused...");
                                        }
                                        if (safeToPlay)
                                        {
                                            // copy audio to local...
                                            string audioFile = new FileInfo(playThisFile).DirectoryName + "\\" +
                                                _dgISOContentView["recordedFileNameDataGridViewTextBoxColumn", e.RowIndex].Value.ToString();
                                            Log.LogWrite("Step 4. Retrieve or reuse this audio file locally: " + audioFile);

                                            if (!File.Exists(audioFile))
                                            {
                                                LoadISOContentToLocal(audioFile);
                                                toolStripProgressBar.PerformStep(); // 3 
                                                Application.DoEvents();
                                            }
                                            else
                                            {
                                                Log.LogWrite("This audio file has been downloaded previously and will be reused...");
                                            }

                                            Log.LogWrite("Step 5. Start movie...");
                                            StartMovie(movie);
                                            toolStripProgressBar.PerformStep(); //4
                                            Application.DoEvents();
                                            //_autoEventLoadAudioVideoFileInGrid.WaitOne();
                                        }
                                        else
                                        {
                                            Log.LogWrite("Unable to play video...");
                                        }
                                    }
                                    catch (Exception ex)
                                    {
                                        _msgs = ErrorMessageString(ex);
                                        Log.LogWrite(_msgs);
                                        Application.DoEvents(); //TODO:
                                        MessageBox.Show(string.Format(RES.Resources.RES_UnableToOpenVideoFile));
                                    }
                                    finally
                                    {
                                        Log.LogWrite("Step 6. Clean up...");
                                        Cursor.Current = Cursors.Default;
                                        toolStripStatusLabel.Text = saveToolStripStatusText;
                                        toolStripProgressBar.Visible = false;
                                        toolStripProgressBar.Step = progressBarDefaultStep;
                                        Application.DoEvents();
                                    }
                                }
                                break;
                        }
                    }
                    else
                    {
                        Log.LogWrite("Unable to retrieve media: " + fileWeNeed);
                    }
                }
            }
            catch (Exception ex)
            {
                Log.LogWrite("Error during cell double-click...");
                _msgs = ErrorMessageString(ex);
                Log.LogWrite(_msgs);
            }
            finally
            {
                Log.LogWrite("Exit _dgISOContentView_CellContentDoubleClick()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void SRIPArchiveClientForm_FormClosing(object sender, FormClosingEventArgs e)
        {
            Properties.Settings.Default.WindowWidth = this.Width;
            Properties.Settings.Default.WindowHeight = this.Height;
            Properties.Settings.Default.WindowLocationX = this.Location.X;
            Properties.Settings.Default.WindowLocationY = this.Location.Y;
            Properties.Settings.Default.WindowState = Convert.ToString(this.WindowState, CultureInfo.CurrentCulture);
            Properties.Settings.Default.Save();

            Log.LogWrite("Exiting Archive Client Tool...\r\n===#########**FINISHED**ARCHIVE**############===\r\n");
            Log.CloseLogger();
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void SRIPArchiveClientForm_FormClosed(object sender, FormClosedEventArgs e)
        {
            if (Stop != null && Stop.GetInvocationList().Length > 0)
                Stop();
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtUserName_TextChanged(object sender, EventArgs e)
        {
            if (txtUserName.Text.Length.Equals(0)) btnSaveLocation.Enabled = false;
            else btnSaveLocation.Enabled = true;
            _userName = txtUserName.Text; // cross thread access...
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtPassword_TextChanged(object sender, EventArgs e)
        {
            _password = txtPassword.Text; // cross thread access...
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void dtpStartDate_ValueChanged(object sender, EventArgs e)
        {
            dtpStartDate_Validated(sender as Control, e);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void dtpStartTime_ValueChanged(object sender, EventArgs e)
        {
            dtpStartTime_Validated(sender as Control, e);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void dtpEndDate_ValueChanged(object sender, EventArgs e)
        {
            dtpStartDate_Validated(sender as Control, e);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void dtpEndTime_ValueChanged(object sender, EventArgs e)
        {
            dtpStartTime_Validated(sender as Control, e);
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void chkBoxArchiveRecylceBin_CheckedChanged(object sender, EventArgs e)
        {
            _archiveRecycleBinContents = chkBoxArchiveRecylceBin.Checked;

            dtpStartDate.Enabled =
            dtpStartTime.Enabled =
            dtpEndDate.Enabled =
            dtpEndTime.Enabled = !_archiveRecycleBinContents;
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtOutputLocation_TextChanged(object sender, EventArgs e)
        {
            _outputLocation = txtOutputLocation.Text; // cross thread access...         
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtMediaVolumeName_TextChanged(object sender, EventArgs e)
        {
            _mediaVolumeName = txtMediaVolumeName.Text; // cross thread access...
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtUXURL_TextChanged(object sender, EventArgs e)
        {
            // end with a forward slash                     
            //_uxURL = txtUXURL.Text; // cross thread access...
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtWebServiceURL_TextChanged(object sender, EventArgs e)
        {
            // ends without a slash          
            _callRecordingURL = txtWebServiceURL.Text; // cross thread access...             
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtISOFileStructure_TextChanged(object sender, EventArgs e)
        {
            // ends with a backslash
            _isoDirectoryLayout = txtISODirectoryLayout.Text; // cross thread access...         
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void txtCustomFileName_TextChanged(object sender, EventArgs e)
        {
            _outputISOFileName = txtCustomFileName.Text;
        }
        /// <summary>
        /// 
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void btnSaveLocation_Click(object sender, EventArgs e)
        {
            // only show directroy dialog...
            if (_fbDlg.ShowDialog(this) == DialogResult.OK)
            {
                //
                // fix txtUserName to handle occasions where
                // the user name is a domain name...
                //
                var fixedTxtUserName = txtUserName.Text.Replace("\\", "_");
                //
                // auto-gen an output file name and
                // place it in the selected directory...
                //    
                txtOutputLocation.Text = CreateISOImageOutputFileName(_fbDlg.SelectedPath + "\\" + fixedTxtUserName + "_", "0", true);
            }
        }
        /// <summary>
        /// start/stop/restore all happen here...
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void btnCreateOutputFile_Click(object sender, EventArgs e)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter btnCreateOutputFile_Click()...");
            try
            {
                if (btnCreateOutputFile.Text.Equals(RES.Resources.RES_BTN_Restore))
                {
                    RestoreSelectedCalls();
                    return;
                }

                if (!_bgWorkerWebService.CancellationPending)
                {
                    if (!btnCreateOutputFile.Text.Equals(RES.Resources.RES_BTN_Cancel))
                    {
                        if (ValidateUIContent())
                        {
                            lock (_objectLock)
                            {
                                _imageRepository = null;
                         
                                _isoIterateImageRepository =
                                _isoImageRepositoryIndex = 0;

                                _dictionaryOfArchiveDataTableContent = null;
                                _dictionaryOfArchiveDataTableContent = new Dictionary<int, List<FileImageInfo.ArchiveData>>();

                                _imageRepositoryList = null;
                                _imageRepositoryList = new List<ImageRepository> {new ImageRepository()};
                                _imageRepository = _imageRepositoryList[_isoImageRepositoryIndex];
                            }

                            _timeRemainingEstimates.Reset(); _timeRemainingEstimates.Start();
                            _elapsedFileDownloadIsoCreationTime.Reset(); _elapsedFileDownloadIsoCreationTime.Start();

                            _arcDownLoadTimeOutError =
                            _cancellationISOWriter =
                            _safeToDeleteTempDirectory =
                            _cancellationWebServiceError =
                            _filesNotFoundError =
                            _cancelledCOMRunTimeError = false;

                            toolStripStatusLabel.Text = string.Empty;
                            toolStripProgressBar.Value = toolStripProgressBar.Minimum;
                            toolStripProgressBar.Style = ProgressBarStyle.Marquee;
                            BeginArchiveToIsoWriterProcessor();
                        }
                    }
                    else
                    {
                        if (_bgWorkerISOWriter.IsBusy)
                        {
                            _msgs = string.Format(RES.Resources.RES_CancelingISOWriterPleaseWait);
                            Log.LogWrite("btnCreateOutputFile_Click(cancel): _bgWorkerISOWriter.IsBusy... " + _msgs);
                            toolStripStatusLabel.Text = _msgs;
                            _cancellationISOWriter = true;
                            _bgWorkerISOWriter.CancelAsync();
                            this.Stop();
                            btnCreateOutputFile.Enabled = false;
                        }
                        if (_bgWorkerWebService.IsBusy)
                        {
                            _msgs = string.Format(RES.Resources.RES_CancelingDataRetrievalServicePleaseWait);
                            Log.LogWrite("btnCreateOutputFile_Click(cancel): _bgWorkerWebService.IsBusy... " + _msgs);
                            toolStripStatusLabel.Text = _msgs;
                            UpdateEventViewer(_msgs);
                            _cancellationPendingWebService = true;
                            _bgWorkerWebService.CancelAsync();
                            btnCreateOutputFile.Enabled = false;
                        }
                        if (_bgWorkerAddFilesToImageRepository.IsBusy)
                        {
                            _msgs = string.Format(RES.Resources.RES_CancelingFileParserPleaseWait);
                            Log.LogWrite("btnCreateOutputFile_Click(cancel): _bgWorkerAddFilesToImageRepository.IsBusy... " + _msgs);
                            toolStripStatusLabel.Text = _msgs;
                            UpdateEventViewer(_msgs);
                            _cancellationPendingAddingFilesToImageRepository = true;
                            _bgWorkerAddFilesToImageRepository.CancelAsync();
                            btnCreateOutputFile.Enabled = false;
                        }
                    }
                }
            }
            finally
            {
                Log.LogWrite("Exit btnCreateOutputFile_Click()... " + FormatElapsedTime(stopwatch));
            }
        }

        ////////////////////////////////////////////////////////////////////////// 
        #endregion


        #region Background Worker Helpers...
        ////////////////////////////////////////////////////////////////////////// 

        /// <summary>
        /// kicks off the code to create the ISO image
        /// </summary>
        private void BeginArchiveToIsoWriterProcessor()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter BeginArchiveToIsoWriterProcessor()...");
            try
            {
                _cancellationPendingWebService = false;
                RunArchiveWebServiceProcessor();
            }
            catch (System.Runtime.InteropServices.COMException ex)
            {
                _cancelledCOMRunTimeError = true;

                if (ex.ErrorCode == -1062555360)
                {
                    _msgs = string.Format(RES.Resources.RES_MediaSizeCouldBeTooSmallForTheAmountData, _imageRepository.SizeBeforeFormatting);
                    PopulateStatusTextBox(_msgs, true);
                    UpdateEventViewer(_msgs);
                }
                else
                {
                    _msgs = string.Format(RES.Resources.RES_UnableToCreateImage, ex.Message);
                    PopulateStatusTextBox(_msgs, true);
                    UpdateEventViewer(_msgs);
                }
                File.Delete(txtOutputLocation.Text);
            }
            catch (SRIPArchiveClientFormException bEx)
            {
                this.Stop();
                DisableControls(false);
                PopulateStatusTextBox(bEx.Message, true);
            }
            catch (Exception ex)
            {
                if (!this.IsDisposed)
                {
                    if (_imageRepository.Cancel)
                        toolStripStatusLabel.Text = "Canceled";
                    else
                    {
                        toolStripStatusLabel.Text = "Exception";
                        PopulateStatusTextBox(ex.Message, true);
                    }
                }
                File.Delete(txtOutputLocation.Text);

                _msgs = ErrorMessageString(ex);
                UpdateEventViewer(_msgs, EventLogEntryType.Warning);
            }
            finally
            {
                if (_imageRepository.Cancel)
                    File.Delete(txtOutputLocation.Text);
                Log.LogWrite("Exit BeginArchiveToIsoWriterProcessor()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// Runs process in background thread
        /// </summary>
        private void RunArchiveWebServiceProcessor()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter RunArchiveWebServiceProcessor()...");

            try
            {

                btnCreateOutputFile.Enabled = true;

                _msgs = string.Format(RES.Resources.RES_RestoreStatusSectionDivider);
                if (txtBoxStatus.Text.Length > 4)
                    PopulateStatusTextBox(_msgs, true);
                else
                    PopulateStatusTextBox(_msgs, false);

                _msgs = string.Format(RES.Resources.RES_StartDateTime, DateTime.Now.ToString());
                PopulateStatusTextBox(_msgs, true);

                _msgs = string.Format(RES.Resources.RES_AuthenticatingRequestPleaseWait);
                PopulateStatusTextBox(_msgs, true);

                DisableControls(true);

                // but first we need to download the MP3 files...
                _bgWorkerWebService.RunWorkerAsync();
            }
            finally
            {
                Log.LogWrite("Exit RunArchiveWebServiceProcessor()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// Compares the list of the files
        /// that were downloaded from the 
        /// server to the list of files that 
        /// were captured in ISO image list
        /// </summary>
        private int CompareDownloadListToISOList()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter CompareDownloadListToISOList()...");

            try
            {
                // complete list sans dupes of all files we were told to download
                List<string> listFilesToDownload = new List<string>();
                // complete list sans dupes of callID's from CallArray
                List<int> listAudioCallIds = new List<int>();
                // complete list sans dupes of callID's from VideoArray
                List<int> listVideoCallIds = new List<int>();
                // complete list of files that we were told to download - but didn't!
                List<string> listNoMatchingAudioFileInISOImageList = new List<string>();
                // complete list of callID's associated with video that didn't have a matching audio 
                List<int> listNoMatchingAudioCallIdsForVideoCallIds = new List<int>();
                // get the download path that was used
                string path = Path.GetDirectoryName(ObjFileImageInfo.PathsAndFileNames[0]);

                #region Note...
                //////////////////////////////////////////////////
                /*
                 * What is the problem here?
                 * Using our test data, we encountered situations
                 * where our search criteria could return 
                 * video records without a corresponding audio record.
                 * 
                 * What does that mean?
                 * SmartRecord records both audio and video files for each
                 * call - or at least it can. SmartRecord *always* makes
                 * an audio file. Video may or may not be available. 
                 * 
                 * Still, what exactly happened that's a problem?
                 * Ok, I don't know how we did it, but our test
                 * data has video files for a call, but the date/time
                 * stamp is different than the audio files for that
                 * same call. So, depending on how narrow the search
                 * criteria is, we could return videos that don't have
                 * audio because the audio files datetime stamp was outside
                 * of the search criteria and vice versa - audio without
                 * its video.
                 * 
                 * Anyway, we added this method to handle this anomaly...
                 * 
                 */
                //////////////////////////////////////////////////
                #endregion

                // First, get the callID's for each of the
                // video files we were suppose to download...
                if (null != ScreenRecordingVideoArray)
                {
                    foreach (ScreenRecordingForArchival s in ScreenRecordingVideoArray.ToList())
                    {
                        //if (s.RecordingFileLocation == null) continue;

                        string f = path + "\\" + s.RecordingFileLocation.Substring(s.RecordingFileLocation.LastIndexOf("\\", StringComparison.Ordinal) + 1);
                        if (listFilesToDownload.Contains(f).Equals(false)) listFilesToDownload.Add(f);
                        if (listVideoCallIds.Contains(s.CallId).Equals(false)) listVideoCallIds.Add(s.CallId);
                    }
                }

                // Next, get the callID's for each of the
                // audio files we were suppose to download...
                if (null != CallsArray)
                {
                    foreach (RecordedCalls s in CallsArray.ToList())
                    {
                        //if (s.RecordingFileLocation == null) continue;

                        string f = path + "\\" + s.RecordingFileLocation.Substring(s.RecordingFileLocation.LastIndexOf("\\", StringComparison.Ordinal) + 1);
                        if (listFilesToDownload.Contains(f).Equals(false)) listFilesToDownload.Add(f);
                        if (listAudioCallIds.Contains(s.CallID).Equals(false)) listAudioCallIds.Add(s.CallID);
                    }
                }

                //
                // Now, look for any item we were 
                // told to download, but didn't!
                listNoMatchingAudioFileInISOImageList = listFilesToDownload.Except(ObjFileImageInfo.PathsAndFileNames).ToList<string>();

                //
                // let the user know we are missing some files...
                foreach (string s in listNoMatchingAudioFileInISOImageList)
                {
                    // make sure we note what we found...
                    if (string.IsNullOrEmpty(s)) continue;
                    PopulateStatusTextBox(string.Format(RES.Resources.RES_NoMatchingAudioFileInISOImageList, s), true);
                }

                //
                // this step is important because here we determine
                // if the missing files are valid...
                if (listNoMatchingAudioFileInISOImageList.Count > 0 &&
                    listVideoCallIds.Count > 0)
                {
                    //
                    // Bummer, we didn't download some files but; 
                    // we may actually have a reason for this snafu.
                    // It appears that there can be some SRF files 
                    // that don't have matching call/audio records. 
                    // This corner case was spotted during local unit 
                    // testing - possibly the result of some bogus data
                    // added to lab server; anyway, to address this 
                    // we will look for anyone in the video list that 
                    // is not in the main call/audio list and 
                    // log our findings...
                    //
                    listNoMatchingAudioCallIdsForVideoCallIds = listVideoCallIds.Except(listAudioCallIds).ToList<int>();
                    PopulateStatusTextBox((string.Format(RES.Resources.RES_CountOfVideosWithoutMatchingAudioCallIDs, listNoMatchingAudioCallIdsForVideoCallIds.Count)), true);
                    bool validExceptions = listNoMatchingAudioFileInISOImageList.Count.Equals(listNoMatchingAudioCallIdsForVideoCallIds.Count);
                    string comments = string.Format(RES.Resources.RES_SameCountAsTheNumberOfFilesNotInIsoFileList,
                        validExceptions ?
                        string.Format(RES.Resources.RES_ValidDownloadExceptions, listNoMatchingAudioCallIdsForVideoCallIds.Count, (_initialCountOfCallsToDownLoad - listNoMatchingAudioCallIdsForVideoCallIds.Count)) :
                        RES.Resources.RES_InvalidDownloadExceptions);
                    PopulateStatusTextBox(comments, true);
                }

                // get the difference...
                return listNoMatchingAudioFileInISOImageList.Count - listNoMatchingAudioCallIdsForVideoCallIds.Count;
            }
            finally
            {
                Log.LogWrite("Exit CompareDownloadListToISOList()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        internal static string ArchiveWebServiceURLPostPend()
        {
            return ConfigurationManager.AppSettings["ArchiveWebService"];
        }

        /// <summary>
        /// generates the index text value
        /// used in the output file names...
        /// </summary>
        /// <param name="mediaCount"> </param>
        /// <returns>0,1,2, etc...</returns>
        private string CreateIndexTextValue(int mediaCount)
        {
            return mediaCount.ToString(CultureInfo.InvariantCulture);
        }

        //////////////////////////////////////////////////////////////////////////  
        #endregion

        #region ISO Writer Progress Tracking...
        //////////////////////////////////////////////////////////////////////////
        /// <summary>
        /// track event updates and show progress in 
        /// progress control during Format phase
        /// </summary>
        /// <param name="o1"></param>
        /// <param name="o2"></param>
        void AsyncFormattingEvent(object o1, object o2)
        {
            Invoke(new DiscFormat2Data_EventsHandler(FormattingEvent), new Object[] { o1, o2 });
        }
        void FormattingEvent(object o1, object o2)
        {
            IProgressItem it = o1 as IProgressItem;
            int i = (int)(Convert.ToSingle(o2) * 100);
            this.toolStripProgressBar.Value = 100 + i;

            if (it != null && (!it.Description.Equals(_holdFormattingMsg)))
            {
                toolStripStatusLabel.Text = string.Format(RES.Resources.RES_PctFormatting
                    , (this.toolStripProgressBar.Value / 2).ToString()
                    , it.Description);
            }
            lock (_objectLock) { _holdFormattingMsg = it.Description; }
        }
        /// <summary>
        /// track event updates and show progress in
        /// progress control during Repository processing phase        
        /// </summary>
        /// <param name="o1"></param>
        /// <param name="o2"></param>
        void AsyncRepositoryUpdate(object o1, object o2)
        {
            Invoke(new DiscFormat2Data_EventsHandler(RepositoryUpdate), new Object[] { o1, o2 });
        }
        void RepositoryUpdate(object o1, object o2)
        {
            string file = o1 as string;
            long i = Convert.ToInt64(o2);
            int pos = (int)((double)_imageRepository.ActualSize / _imageRepository.SizeBeforeFormatting * 100);
            toolStripProgressBar.Value = pos;

            if (!file.Equals(_holdUpdatingMsg))
            {
                toolStripStatusLabel.Text = string.Format(RES.Resources.RES_PctAdding
                    , (toolStripProgressBar.Value / 2).ToString()
                    , file
                    , i);
            }
            lock (file) { _holdUpdatingMsg = file; }
        }
        //////////////////////////////////////////////////////////////////////////
        #endregion

        //////////////////////////////////////////////////////////////////////////

        //////////////////////////////////////////////////////////////////////////

        #region GUI, Configurations, etc utilities...
        //////////////////////////////////////////////////////////////////////////

        /// <summary>
        /// update tz data with zip file content...
        /// </summary>
        /// <returns></returns>
        private bool UpdateTimeZoneFiles()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter UpdateTimeZoneFiles()...");

            bool results = true;

            try
            {
                _timeZoneDirectoryExclusionList.Clear();
                _timeZoneDirectoryExclusionList.Add(".SQL");
                _timeZoneDirectoryExclusionList.Add(".ZIP");
                _timeZoneDirectoryExclusionList.Add(".SCC");
                _timeZoneDirectoryExclusionList.Add(".BAK");
                _timeZoneDirectoryExclusionList.Add("TIMEZONEFUNCTIONS.DLL");
                _timeZoneDirectoryExclusionList.Add("COPYOLSONFILES");

                string tzDataDir = ConfigurationManager.AppSettings["TzDataDir"].Split('\\')[0];
                string windowsToOlsonMapDir = ConfigurationManager.AppSettings["WindowsToOlsonMapDir"].Split('\\')[0];
                string destinationDir = "C:" + ConfigurationManager.AppSettings["DestinationDir"];



                string zipFileFullName = new FileInfo(Application.ExecutablePath).DirectoryName +
                                         "\\OlsonTimeZone.iso.zip";

                if (File.Exists(zipFileFullName).Equals(false))
                {
                    results = false;
                    Log.LogWrite("File not found: " + zipFileFullName);
                    return results;
                }


                using (ZipFile zip = ZipFile.Read(zipFileFullName))
                {
                    try
                    {
                        foreach (ZipEntry e in zip)
                        {
                            // TzData Folder...
                            if (e.FileName.ToLower().Contains(tzDataDir.ToLower()))
                            {
                                string f = ValidatedTimeZoneFile(new FileInfo(e.FileName).Name);
                                if (!string.IsNullOrEmpty(f))
                                {
                                    // verifying this is latest...
                                    string baseFolder = destinationDir + tzDataDir + "\\";
                                    // @"C:\CTI Group\TimeZone\v2-0-4\tzdata\";
                                    Log.LogWrite(string.Format("CURRENT - {0} MODIFY TIME: {1}", baseFolder + f, File.GetLastWriteTime(baseFolder + f).ToString("s")));
                                    Log.LogWrite(string.Format("UPDATE - {0} MODIFY TIME: {1}", e.FileName, e.LastModified.ToString("s")));
                                    if (File.GetLastWriteTime(baseFolder + f).CompareTo(DateTime.Parse(e.LastModified.ToString())) < 0)
                                    {
                                        try
                                        {
                                            // handle file readonly attributes...
                                            FileAttributesHandler(f, baseFolder);

                                            using (FileStream fstrm = new FileStream(baseFolder + f, FileMode.OpenOrCreate, FileAccess.ReadWrite))
                                            {
                                                e.Extract(fstrm);
                                                Log.LogWrite(string.Format("Replaced: {0} - {1} With: {2} - {3}"
                                                    , string.IsNullOrEmpty(f) ? e.FileName : f
                                                    , string.IsNullOrEmpty(f)
                                                    ? "N/A"
                                                    : File.GetLastWriteTime(baseFolder + f).ToString()
                                                    , e.FileName, e.LastModified));
                                                continue;
                                            }
                                        }
                                        catch (Exception ex)
                                        {
                                            Log.LogWrite(ErrorMessageString(ex));
                                        }
                                    }
                                    else
                                    {
                                        Log.LogWrite("Update not required...");
                                    }
                                }
                            }

                            // WindowsToOlsonMap Folder...
                            if (e.FileName.ToLower().Contains(windowsToOlsonMapDir.ToLower()))
                            {
                                string f = ValidatedTimeZoneFile(new FileInfo(e.FileName).Name);
                                if (!string.IsNullOrEmpty(f))
                                {
                                    // verifying this is latest...
                                    string baseFolder = destinationDir + windowsToOlsonMapDir + "\\";
                                    // @"C:\CTI Group\TimeZone\v2-0-4\windowsToOlsonMapDir\";
                                    Log.LogWrite(string.Format("CURRENT - {0} MODIFY TIME: {1}", baseFolder + f, File.GetLastWriteTime(baseFolder + f).ToString("s")));
                                    Log.LogWrite(string.Format("UPDATE - {0} MODIFY TIME: {1}", e.FileName, e.LastModified.ToString("s")));
                                    if (File.GetLastWriteTime(baseFolder + f).CompareTo(DateTime.Parse(e.LastModified.ToString())) < 0)
                                    {
                                        try
                                        {
                                            // handle file readonly attributes...
                                            FileAttributesHandler(f, baseFolder);

                                            using (FileStream fstrm = new FileStream(baseFolder + f
                                                , FileMode.OpenOrCreate
                                                , FileAccess.ReadWrite))
                                            {
                                                e.Extract(fstrm);
                                                Log.LogWrite(string.Format("Replaced: {0} - {1} With: {2} - {3}"
                                                    , string.IsNullOrEmpty(f) ? e.FileName : f
                                                    , string.IsNullOrEmpty(f)
                                                    ? "N/A"
                                                    : File.GetLastWriteTime(baseFolder + f).ToString()
                                                    , e.FileName
                                                    , e.LastModified));
                                                continue;
                                            }
                                        }
                                        catch (Exception ex)
                                        {
                                            Log.LogWrite(ErrorMessageString(ex));
                                        }
                                    }
                                    else
                                    {
                                        Log.LogWrite("Update not required...");
                                    }
                                }
                            }
                        }
                    }
                    catch (Exception ex)
                    {
                        Log.LogWrite(ErrorMessageString(ex));
                    }
                }
            }
            finally
            {
                Log.LogWrite("Exit UpdateTimeZoneFiles()... " + FormatElapsedTime(stopwatch));
            }

            return results;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="f"></param>
        /// <param name="baseFolder"></param>
        private static void FileAttributesHandler(string f, string baseFolder)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter FileAttributesHandler()...");
            string file = baseFolder + f;
            try
            {
                Log.LogWrite("Check file attributes...");
                // check whether a file is read only 
                bool isReadOnly = IsReadOnlyFile(file);
                Log.LogWrite(string.Format("File: {0} is readonly? {1}", file, isReadOnly));

                // check whether a file is hidden                                            
                Log.LogWrite(string.Format("File: {0} is hidden? {1}", file, IsHiddenFile(file)));

                // check whether a file has archive attribute                                            
                Log.LogWrite(string.Format("File: {0} is archive? {1}", file, IsArchiveFile(file)));

                // check whether a file is system file                                            
                Log.LogWrite(string.Format("File: {0} is system file? {1}", file, IsSystemFile(file)));

                // clear all file attributes
                if (isReadOnly)
                {
                    Log.LogWrite("Need to clear attributes...");
                    ClearFileAttributes(file);

                    Log.LogWrite(string.Format("File: {0} is readonly? {1}", file, IsReadOnlyFile(file)));

                    // check whether a file is hidden                                            
                    Log.LogWrite(string.Format("File: {0} is hidden? {1}", file, IsHiddenFile(file)));

                    // check whether a file has archive attribute                                            
                    Log.LogWrite(string.Format("File: {0} is archive? {1}", file, IsArchiveFile(file)));

                    // check whether a file is system file                                            
                    Log.LogWrite(string.Format("File: {0} is system file? {1}", file, IsSystemFile(file)));
                }

            }
            catch (Exception ex)
            {
                Log.LogWrite(ErrorMessageString(ex));
            }
            finally
            {
                var ts = stopwatch.Elapsed;
                Log.LogWrite("Exit FileAttributesHandler()... " + string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                                                                             , ts.Hours
                                                                             , ts.Minutes
                                                                             , ts.Seconds
                                                                             , ts.Milliseconds / 10));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="file"></param>
        private static void ClearFileAttributes(string file)
        {
            File.SetAttributes(file, FileAttributes.Normal);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="file"></param>
        /// <returns></returns>
        private static bool IsReadOnlyFile(string file)
        {
            return ((File.GetAttributes(file) & FileAttributes.ReadOnly) == FileAttributes.ReadOnly);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="file"></param>
        /// <returns></returns>
        private static bool IsHiddenFile(string file)
        {
            return ((File.GetAttributes(file) & FileAttributes.Hidden) == FileAttributes.Hidden);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="file"></param>
        /// <returns></returns>
        private static bool IsArchiveFile(string file)
        {
            return ((File.GetAttributes(file) & FileAttributes.Archive) == FileAttributes.Archive);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="file"></param>
        /// <returns></returns>
        private static bool IsSystemFile(string file)
        {
            return ((File.GetAttributes(file) & FileAttributes.System) == FileAttributes.System);
        }


        /// <summary>
        /// 
        /// </summary>
        /// <param name="p"></param>
        /// <returns></returns>
        private string ValidatedTimeZoneFile(string fileName)
        {
            string validFile = fileName;

            bool invalid = false;
            try
            {
                invalid = _timeZoneDirectoryExclusionList.Contains(new FileInfo(fileName).Name.ToUpper());
                if (invalid.Equals(false)) invalid = _timeZoneDirectoryExclusionList.Contains(new FileInfo(fileName).Extension.ToUpper());
                if (invalid) validFile = string.Empty;
            }
            catch (Exception ex)
            {
                Log.LogWrite(ErrorMessageString(ex));
                validFile = string.Empty;
            }
            return validFile;
        }




        /// <summary>
        /// populates the timezone dropdown list
        /// </summary>
        /// <returns></returns>
        private List<string> PopulateTZList()
        {
            List<string> tz = new List<string>();
            foreach (TZ.Business_Objects.WindowsToOlson_NameMap wtom in TimeZoneData.WindowsToOlsonNameMap)
            {
                tz.Add(wtom.Windows_Time_Zone_Name);
            }
            return tz;
        }

        /// <summary>                
        /// Restore calls requires that we provide
        /// all the parameters that AddRecordedCalls;
        /// This method opens the Restore dialog...
        /// TODO: Needs to be updated to restore video files.
        /// </summary>
        private void RestoreSelectedCalls()
        {
            if (_nrOfRowsSelected < 1)
            {
                MessageBox.Show(RES.Resources.RES_NoCallsSelected);
                return;
            }
            SRIPArchiveRestoreForm restoreForm = new SRIPArchiveRestoreForm(
                _callRecordingURL + ArchiveWebServiceURLPostPend()
                , _maxAttemptsToContactServer
                , _isoReaderInputFile
                , _isoReaderOutputLocation
                , _dgISOContentView
                , _nrOfRowsSelected
                , _currentTimeZoneSelected
                , _callRecordingURL
                , _maxReceivedMsgSize);

            restoreForm.ShowDialog();
        }

        /// <summary>
        /// updates checkbox item then reloads gridview        
        /// </summary>
        private void SelectAllItemsInViewerGrid()
        {
            try
            {
                Cursor = Cursors.WaitCursor;

                string csvFile = LoadISOContentToLocal(RES.Resources.RES_IndexCSVFileName);
                if (!string.IsNullOrEmpty(csvFile))
                {
                    try
                    {
                        bool includesVolumeName = true;
                        using (DataTable dt = ParseCSVComplex(csvFile))
                        {
                            foreach (DataRow dr in dt.Rows)
                            {
                                dr["UploadCall"] = _selectAllRows;
                                try
                                {
                                    // Bug: Time field doesn't include ms
                                    dr["CallDateTime"] = (TimeZoneData
                                        .ConvertUtcToTimeZone(
                                            new DateTime(Convert.ToInt64(dr["CallDateTime"].ToString()))
                                            , comboBoxTimeZoneList.SelectedItem.ToString()))
                                        .Value.ToString("o");
                                }
                                catch
                                {
                                    dr["CallDateTime"] =
                                        //
                                        // Bug: Time field doesn't sort correctly because it
                                        //      is rendered in datagridview as a string. To
                                        //      fix this we need to render the datetime as "o"                                   
                                        //
                                        Convert.ToDateTime(
                                            TimeZoneData.ConvertUtcToTimeZone(
                                                Convert.ToDateTime(dr["CallDateTime"].ToString(),
                                                    CultureInfo.InvariantCulture)
                                                , comboBoxTimeZoneList.SelectedItem.ToString()).ToString())
                                            .ToString("o").Replace("Z", "");
                                }
                                if (includesVolumeName)
                                {
                                    try
                                    {
                                        _contentsForVolumeName = dr["VolumeName"].ToString();
                                    }
                                    catch
                                    {
                                        includesVolumeName = false;
                                    }
                                }
                            }

                            _bindingSource.DataSource = dt;
                            _dgISOContentView.DataSource = _bindingSource;

                            // if necessary, reset search filter...
                            if (!string.IsNullOrEmpty(toolStripTextBoxFilter.Text.Trim()))
                                toolStripTextBoxFilter_TextChanged(this, null);

                            if (_selectAllRows)
                            {
                                btnSelectAll.Text = _strSelectNone;
                                _nrOfRowsSelected = _dgISOContentView.Rows.Count - 1;
                            }
                            else
                            {
                                btnSelectAll.Text = _strSelectAll;
                                _nrOfRowsSelected = 0;
                            }
                        }
                    }
                    catch (SRIPArchiveClientFormException e)
                    {
                        _msgs = e.Message;
                    }
                    catch { }
                }
            }
            finally
            {
                PopulateStatusTextBox("Grid " + _msgs, true);
                Cursor = Cursors.Default;
            }
        }
        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private bool ValidateUIContent()
        {
            bool ok = true;

            ClearErrorsFirst();

            if (ok) ok = ValidateParameterPage();
            if (ok) ok = ValidateConfigPage();
            if (ok) ok = ValidateExistenceOfISODirectoryLayout();
            if (ok) ok = ValidateExistenceOfISOOutputDirectory();
            if (ok) ok = ValidateExistenceOfViewerOutputDirectory();

            return ok;
        }

        /// <summary>
        /// clear errors and other global fields here
        /// </summary>
        private void ClearErrorsFirst()
        {
            _holdUpdatingMsg =
            _holdFormattingMsg = string.Empty;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private bool ValidateParameterPage()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter ValidateParameterPage()...");

            bool ok = true;
            try
            {
                //
                // verify parameter page content...
                //
                if (string.IsNullOrEmpty(txtUserName.Text.Trim()))
                {
                    Log.LogWrite("1 of 6  IsNullOrEmpty(txtUserName.Text.Trim())");
                    tabControlISOWriter.SelectedIndex = 0;
                    toolStripStatusLabel.Text = string.Format(RES.Resources.RES_ErrorUserNameNotProvided);
                    txtUserName.Focus();
                    txtUserName_Validated(txtUserName as Control, null);
                    ok = false;
                }

                if (ok && string.IsNullOrEmpty(txtPassword.Text.Trim()))
                {
                    Log.LogWrite("2 of 6 IsNullOrEmpty(txtPassword.Text.Trim())");
                    tabControlISOWriter.SelectedIndex = 0;
                    toolStripStatusLabel.Text = string.Format(RES.Resources.RES_ErrorPasswordNotProvided);
                    txtPassword.Focus();
                    ok = false;
                    txtPassword_Validated(txtPassword as Control, null);
                }
                DateTime sd = SetDate(dtpStartDate, dtpStartTime);
                DateTime ed = SetDate(dtpEndDate, dtpEndTime);
                if (ok && (sd.Ticks > ed.Ticks))
                {
                    Log.LogWrite("3 of 6 (startdate.Ticks > enddate.Ticks) ");
                    tabControlISOWriter.SelectedIndex = 0;
                    if (dtpStartDate.Value > dtpEndDate.Value)
                    {
                        toolStripStatusLabel.Text = string.Format(RES.Resources.RES_ErrorStartDateGreaterThanEndDate);
                        dtpStartDate.Focus();
                        dtpStartDate_Validated(dtpStartDate as Control, null);
                    }
                    else if (dtpStartTime.Value > dtpEndTime.Value)
                    {
                        toolStripStatusLabel.Text = string.Format(RES.Resources.RES_ErrorStartTimeGreaterThanEndTime);
                        dtpStartTime.Focus();
                        dtpStartTime_Validated(dtpStartTime as Control, null);
                    }
                    ok = false;
                }
                if (ok && (dtpEndDate.Value.Subtract(dtpStartDate.Value).Days > _archiveNumberOfDaysLimit))
                {
                    Log.LogWrite("4 of 7 endDate.Value.Subtract(startDate.Value).Days > _archiveNumberOfDaysLimit)) ");
                    var over = dtpEndDate.Value.Subtract(dtpStartDate.Value).Days - (_archiveNumberOfDaysLimit);
                    var validStartDate = dtpStartDate.Value.AddDays(over);
                    toolStripStatusLabel.Text = string.Format(Resources.RES_Search_Date_Range_Greater_Than_Max, _archiveNumberOfDaysLimit, validStartDate);
                    dtpStartDate.Focus();
                    dtpStartDate_Validated(dtpStartDate as Control, null);
                    ok = false;
                }
                if (ok && string.IsNullOrEmpty(txtOutputLocation.Text.Trim()))
                {
                    Log.LogWrite("5 of 7 IsNullOrEmpty(txtOutputLocation.Text.Trim()) ");
                    tabControlISOWriter.SelectedIndex = 0;
                    toolStripStatusLabel.Text = string.Format(RES.Resources.RES_ErrorOutputLocationNotProvided);
                    btnSaveLocation.Focus();
                    txtOutputLocation_Validated(txtOutputLocation as Control, null);
                    ok = false;
                }
                if (ok && string.IsNullOrEmpty(txtMediaVolumeName.Text.Trim()))
                {
                    Log.LogWrite("6 of 7 IsNullOrEmpty(txtMediaVolumeName.Text.Trim())");
                    tabControlISOWriter.SelectedIndex = 0;
                    toolStripStatusLabel.Text = string.Format(RES.Resources.RES_ErrorOutputVolumeLabelNotProvided);
                    txtMediaVolumeName.Focus();
                    txtMediaVolumeName_Validated(txtMediaVolumeName as Control, null);
                    ok = false;
                }
                if (ok)
                {
                    Log.LogWrite("All Parameter Settings Valid...");
                    //
                    // fix txtUserName to handle occasions where
                    // the user name is a domain name...
                    //
                    var fixedTxtUserName = txtUserName.Text.Replace("\\", "_");
                    txtOutputLocation.Text =
                        CreateISOImageOutputFileName(
                            new FileInfo(txtOutputLocation.Text).DirectoryName + "\\" + fixedTxtUserName + "_", "0",
                            true);
                }
            }
            finally
            {
                Log.LogWrite("Exit ValidateParameterPage()... " + FormatElapsedTime(stopwatch));
            }
            return ok;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private bool ValidateConfigPage()
        {
            bool ok = true;
            //    
            // verify configuration page content...
            //
            /*
            if (string.IsNullOrEmpty(txtUXURL.Text))
            {
                tabControlISOWriter.SelectedIndex = 1;
                toolStripStatusLabel.Text = string.Format("Error: UX URL not provided...");
                txtUXURL.Focus();
                ok = false;
                //pictBoxUXUrlError.Visible = true;
            }
             */
            if (ok && string.IsNullOrEmpty(txtWebServiceURL.Text) || !Uri.IsWellFormedUriString(txtWebServiceURL.Text, UriKind.Absolute))
            {
                tabControlISOWriter.SelectedIndex = 1;
                toolStripStatusLabel.Text = string.Format(RES.Resources.RES_ErrorWebServiceURLNotProvided);
                txtWebServiceURL.Focus();
                txtWebServiceURL_Validated(txtWebServiceURL as Control, null);
                ok = false;
            }
            else
            {
                if (ok && !txtWebServiceURL.Text.EndsWith("/"))
                {
                    txtWebServiceURL.Text += "/";
                }
            }
            if (ok && string.IsNullOrEmpty(txtISODirectoryLayout.Text))
            {
                tabControlISOWriter.SelectedIndex = 1;
                toolStripStatusLabel.Text = string.Format(RES.Resources.RES_ErrorISODirectoryLayoutNotProvided);
                txtISODirectoryLayout.Focus();
                txtISODirectoryLayout_Validated(txtISODirectoryLayout as Control, null);
                ok = false;
            }
            if (ok && UserDirectoryLocalDirectoryMisMatch(txtISODirectoryLayout.Text))
            {
                tabControlISOWriter.SelectedIndex = 1;
                toolStripStatusLabel.Text = string.Format(Resources.SRIPArchiveClientForm_ValidateConfigPage_ISO_Directory_Given_Is_Not_Valid_Path_);
                txtISODirectoryLayout.Focus();
                txtISODirectoryLayout_Validated(txtISODirectoryLayout as Control, null);
                ok = false;
            }
            if (ok)
            {
                /*
                if (!string.IsNullOrEmpty(txtUXURL.Text))
                {
                    // add forward slash if necessary
                    if (txtUXURL.Text.LastIndexOf('/') != (txtUXURL.Text.Length - 1))
                    {
                        txtUXURL.Text += @"/";
                    }
                }
                 */
                /*
                if (!string.IsNullOrEmpty(txtWebServiceURL.Text))
                {
                    // remove forward slash if necessary
                    if (txtWebServiceURL.Text.LastIndexOf('/').Equals(txtWebServiceURL.Text.Length - 1))
                    {
                        txtWebServiceURL.Text = txtWebServiceURL.Text.Remove(txtWebServiceURL.Text.LastIndexOf('/'));
                    }
                    // check for backslash also
                    else if (txtWebServiceURL.Text.LastIndexOf('\\').Equals(txtWebServiceURL.Text.Length))
                    {
                        txtWebServiceURL.Text = txtWebServiceURL.Text.Remove(txtWebServiceURL.Text.LastIndexOf('\\'));
                    }
                }
                 */
                if (!string.IsNullOrEmpty(txtISODirectoryLayout.Text))
                {
                    // add backslash if necessary
                    if (txtISODirectoryLayout.Text.LastIndexOf('\\') != (txtISODirectoryLayout.Text.Length - 1))
                    {
                        txtISODirectoryLayout.Text += '\\';
                    }
                }
            }
            return ok;
        }

        /// <summary>
        /// If the user submits a bogus path name, FileInfo 
        /// will create a path and it will not be what you expect...
        /// </summary>
        /// <param name="localDirectoryName"> </param>
        /// <returns></returns>
        private bool UserDirectoryLocalDirectoryMisMatch(string localDirectoryName)
        {
            var misMatch = false;
            var isoDirectoryLayout = new FileInfo(localDirectoryName).DirectoryName;
            if (isoDirectoryLayout != null)
            {
                try
                {
                    // 
                    // prevent substring errors...
                    misMatch = isoDirectoryLayout.Length > localDirectoryName.Length;
                    if (!misMatch)
                    {
                        var userDirectoryName = localDirectoryName.Substring(0, isoDirectoryLayout.Length);
                        misMatch = !isoDirectoryLayout.Equals(userDirectoryName);
                    }
                }
                catch (Exception ex)
                {
                    misMatch = true;
                    Log.LogWrite("Error: " + ex.Message);
                }
            }
            return misMatch;
        }

        /// <summary>
        /// this is the temp folder where the downloaded
        /// files are placed; this directory structure
        /// will be mainted in the ISO definition
        /// </summary>
        /// <returns></returns>
        private bool ValidateExistenceOfISODirectoryLayout()
        {
            bool ok = true;
            string isoDirectoryLayout = new FileInfo(txtISODirectoryLayout.Text).DirectoryName;
            if (!string.IsNullOrEmpty(isoDirectoryLayout))
            {
                try
                {
                    if (!Directory.Exists(isoDirectoryLayout))
                        Directory.CreateDirectory(isoDirectoryLayout);

                }
                catch
                {
                    _msgs = string.Format(RES.Resources.RES_TempDirectoryDoesNotExist
                        , isoDirectoryLayout);
                    PopulateStatusTextBox(_msgs, true);
                    UpdateEventViewer(_msgs, EventLogEntryType.Error);
                    ok = false;
                    tabControlISOWriter.SelectedIndex = 1;
                }
            }
            return ok;
        }

        /// <summary>
        /// this is where the completed ISO image
        /// will be located
        /// </summary>
        /// <returns></returns>
        private bool ValidateExistenceOfISOOutputDirectory()
        {
            bool ok = true;
            string outputLocationDirectory = new FileInfo(txtOutputLocation.Text).DirectoryName;
            if (!string.IsNullOrEmpty(outputLocationDirectory))
            {
                try
                {
                    // Create the destination path if it doesn't exist
                    if (!Directory.Exists(outputLocationDirectory))
                        Directory.CreateDirectory(outputLocationDirectory);
                }
                catch
                {
                    _msgs = string.Format(RES.Resources.RES_OutputDirectoryDoesNotExist
                        , outputLocationDirectory);
                    PopulateStatusTextBox(_msgs, true);
                    UpdateEventViewer(_msgs, EventLogEntryType.Error);
                    ok = false;
                    tabControlISOWriter.SelectedIndex = 0;
                }
            }
            return ok;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private bool ValidateExistenceOfViewerOutputDirectory()
        {
            bool ok = true;
            string isoFileReaderOutputDir = new FileInfo(txtISOFileReaderOutputDir.Text).DirectoryName;
            if (!string.IsNullOrEmpty(isoFileReaderOutputDir))
            {
                try
                {
                    if (UserDirectoryLocalDirectoryMisMatch(txtISOFileReaderOutputDir.Text))
                    {
                        tabControlISOWriter.SelectedIndex = 2;
                        toolStripStatusLabel.Text = string.Format(Resources.SRIPArchiveClientForm_ValidateConfigPage_ISO_Directory_Given_Is_Not_Valid_Path_);
                        txtISOFileReaderOutputDir.Focus();
                        txtISOFileReaderOutputDir_Validated(txtISOFileReaderOutputDir as Control, null);
                        ok = false;
                    }
                    else
                    {
                        if (!Directory.Exists(isoFileReaderOutputDir))
                            Directory.CreateDirectory(isoFileReaderOutputDir);
                    }
                }
                catch
                {
                    _msgs = string.Format(RES.Resources.RES_TempDirectoryDoesNotExist
                        , isoFileReaderOutputDir);
                    PopulateStatusTextBox(_msgs, true);
                    UpdateEventViewer(_msgs, EventLogEntryType.Error);
                    ok = false;
                    tabControlISOWriter.SelectedIndex = 2;
                }
            }
            return ok;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="e"></param>
        /// <returns></returns>
        private bool ValidISOContentViewerFile(DragEventArgs e)
        {
            var arr = (Array)e.Data.GetData(DataFormats.FileDrop);

            var ok = arr != null;

            // check for data... 
            // check for output directory...
            if (ok && string.IsNullOrEmpty(txtISOFileReaderOutputDir.Text))
            {
                ok = false;
            }
            //
            // check for valid directory
            if (ok && UserDirectoryLocalDirectoryMisMatch(txtISOFileReaderOutputDir.Text))
            {
                tabControlISOWriter.SelectedIndex = 2;
                toolStripStatusLabel.Text = string.Format(Resources.SRIPArchiveClientForm_ValidateConfigPage_ISO_Directory_Given_Is_Not_Valid_Path_);
                txtISOFileReaderOutputDir.Focus();
                txtISOFileReaderOutputDir_Validated(txtISOFileReaderOutputDir as Control, null);
                ok = false;
            }

            // don't accept multiple files...
            if (ok && arr.Length > 1)
            {
                ok = false;
            }
            // verify extension is ".iso" or "*index.csv"
            if (ok)
            {
                var outFileName = arr.GetValue(0) as string;
                if (outFileName != null)
                {
                    var valid = outFileName.LastIndexOf(".iso", StringComparison.Ordinal);
                    if (valid > 0)
                    {
                        var extension = outFileName.Substring(valid);
                        if (!extension.Equals(".iso")) ok = false;
                    }
                    else
                    {
                        var fileName = outFileName;
                        if (!fileName.Contains(Resources.RES_IndexCSVFileName)) ok = false;
                    }
                }
            }
            return ok;
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="disable"></param>
        private void DisableControls(bool disable)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter DisableControls()...");
            Log.LogWrite("Disabling controls now? " + disable);

            try
            {
                if (disable)
                {
                    btnCopyText.Enabled =
                    comboBoxTimeZoneList.Enabled =
                    grpBoxIndexContents.Enabled =
                    grpBoxISOFile.Enabled =
                    grpBoxSettings.Enabled =
                    grpBoxImageDetails.Enabled =
                    grpDateRange.Enabled =
                    grpBoxDiagnostics.Enabled =
                    grpBoxAuthenticate.Enabled = false;
                    btnCreateOutputFile.Text = RES.Resources.RES_BTN_Cancel;
                    toolStripProgressBar.Visible = true;
                }
                else
                {
                    comboBoxTimeZoneList.Enabled =
                    grpBoxIndexContents.Enabled =
                    grpBoxISOFile.Enabled =
                    btnCreateOutputFile.Enabled =
                    grpBoxSettings.Enabled =
                    grpBoxImageDetails.Enabled =
                    grpBoxDiagnostics.Enabled =
                    grpDateRange.Enabled =
                    grpBoxAuthenticate.Enabled = true;
                    btnCreateOutputFile.Text = RES.Resources.RES_BTN_Create;
                    toolStripProgressBar.Visible = false;

                    btnCopyText.Enabled = txtBoxStatus.Text.Trim().Length > 0;

                    if (tabControlISOWriter.SelectedIndex.Equals(2))
                    {
                        btnSelectAll.Visible = true;
                        btnCreateOutputFile.Text = RES.Resources.RES_BTN_Restore;
                        btnSelectAll.Enabled =
                        btnCreateOutputFile.Enabled = (_dgISOContentView.Rows.Count > 1);
                    }
                }
            }
            finally
            {
                Log.LogWrite("Exit DisableControls()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// dispose of the image repository 
        /// </summary>
        /// <param name="frm"></param>
        private void RemoveImageRepositoryObject(ISOFormatter formatter)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter RemoveImageRepositoryObject(...)...");
            try
            {
                bool finished = formatter != null;
                _imageRepository.Update -= AsyncRepositoryUpdate;

                if (formatter != null)
                {
                    var ev = formatter as DiscFormat2Data_Events;
                    if (ev != null)
                    {
                        ev.Update -= AsyncFormattingEvent;
                        this.Stop -= formatter.CancelOp;
                    }

                    (formatter as IDisposable).Dispose();
                    formatter = null;
                }

                this.Stop -= _imageRepository.CancelOp;
                //_imageRepository.Reset();
                _timeRemainingEstimates.Reset();
                _elapsedIsoCreationTime.Reset();

                if (null != _imageRepository)
                    Log.LogWrite(string.Format("Generation of _imageRepository is: {0}", GC.GetGeneration(_imageRepository)));
                else
                    Log.LogWrite(string.Format("_imageRepository is dead.."));

                _imageRepository = null;

            }
            finally
            {
                Log.LogWrite("Exit RemoveImageRepositoryObject()... " + FormatElapsedTime(stopwatch));   
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="wrapUpSuccessful"></param>
        private void RestoreUI(bool wrapUpSuccessful)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();

            Log.LogWrite("1. ISO-PROCESS-ENDING RemoveImageRepositoryObject(): hold XXXXXXXXXX");
            Thread.Sleep(0);
            Log.LogWrite("2. ISO-PROCESS-BEGINING-RESTORE RestoreUI(bool): released XXXXXXXXXX");

            Log.LogWrite("Enter RestoreUI(...)...");
            Log.LogWrite(string.Format("Formatted successfully? {0}", wrapUpSuccessful));
            try
            {
                DisableControls(false);
                UpdateProgressBar(wrapUpSuccessful);
                ClearImageRepositoryList();
                //CallGarbageCollection();

                if (wrapUpSuccessful) UpdateViewerContent();

                _safeToDeleteTempDirectory = true;
                RemoveTempDir();
                ReportObjectGenerations();

                _imageRepository = null;
                CallsArray = null;
                RecycleBinCallsArray = null;
                ObjFileImageInfo = null;
                ScreenRecordingVideoArray = null;

                ReportObjectGenerations();

                TotalElapsedTime();
            }
            finally
            {
                Log.LogWrite("Exit RestoreUI(...)... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// ISO writer completed; restore UI now
        /// </summary>
        /// <param name="formatter"></param>
        private void RestoreUI(ISOFormatter formatter)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();

            Log.LogWrite("1. ISO-PROCESS-ENDING RemoveImageRepositoryObject(): hold XXXXXXXXXX");
            Thread.Sleep(0);
            Log.LogWrite("2. ISO-PROCESS-BEGINING-RESTORE RestoreUI(...): released XXXXXXXXXX");

            Log.LogWrite("Enter RestoreUI(...)...");
            Log.LogWrite(string.Format("Formatted successfully? {0}", (formatter != null ? "Yes" : "No")));
            try
            {
                bool finished = formatter != null;
                DisableControls(false);
                UpdateProgressBar(finished);
                ClearImageRepositoryList();
                //CallGarbageCollection();

                if (finished) UpdateViewerContent();

                _safeToDeleteTempDirectory = true;
                RemoveTempDir();
                ReportObjectGenerations();

                _imageRepository = null;
                CallsArray = null;
                RecycleBinCallsArray = null;
                ObjFileImageInfo = null;
                ScreenRecordingVideoArray = null;

                ReportObjectGenerations();
                

                TotalElapsedTime();
            }
            finally
            {
                Log.LogWrite("Exit RestoreUI(...)... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// web service canceled...
        /// </summary>
        private void RestoreUI()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();

            Log.LogWrite("1. ISO-PROCESS-ENDING RemoveImageRepositoryObject(): hold XXXXXXXXXX");
            Thread.Sleep(0);
            Log.LogWrite("2. ISO-PROCESS-BEGINING-RESTORE RestoreUI(): released XXXXXXXXXX");

            Log.LogWrite("Enter RestoreUI()...");
            try
            {
                DisableControls(false);
                UpdateProgressBar(false);
                ClearImageRepositoryList();

               //CallGarbageCollection();

                _safeToDeleteTempDirectory = true;
                RemoveTempDir();

                ReportObjectGenerations();

                _imageRepository = null;
                CallsArray = null;
                RecycleBinCallsArray = null;
                ObjFileImageInfo = null;
                ScreenRecordingVideoArray = null;

                ReportObjectGenerations();
                TotalElapsedTime();
            }
            finally
            {
                Log.LogWrite("Exit RestoreUI()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        private void ClearImageRepositoryList()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter ClearImageRepositoryList()...");
            try
            {
                var accum = 0;
                var itemIndex = _imageRepositoryList.Count - 1;
                Log.LogWrite(string.Format("ISO image references found {0}", _imageRepositoryList.Count));
                
                while (itemIndex > -1)
                {
                    using (_imageRepositoryList[itemIndex])
                    {   
                        _imageRepositoryList[itemIndex] = null;
                        --itemIndex;
                        accum++;
                    }
                }

                Log.LogWrite(string.Format("ISO image references cleared {0}", accum));
                _imageRepositoryList.Clear();
                _imageRepositoryList = null;
            }
            finally
            {
                Log.LogWrite("Exit ClearImageRepositoryList()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        private void ReportObjectGenerations()
        {
            if (null != CallsArray)
                Log.LogWrite(string.Format("Generation of CallsArray is: {0}", GC.GetGeneration(CallsArray)));
            else
                Log.LogWrite(string.Format("CallsArray is dead.."));

            if (null != RecycleBinCallsArray)
                Log.LogWrite(string.Format("Generation of RecycleBinCallsArray is: {0}", GC.GetGeneration(RecycleBinCallsArray)));
            else
                Log.LogWrite(string.Format("RecycleBinCallsArray is dead.."));

            if (null != ObjFileImageInfo)
                Log.LogWrite(string.Format("Generation of ObjFileImageInfo is: {0}", GC.GetGeneration(ObjFileImageInfo)));
            else
                Log.LogWrite(string.Format("ObjFileImageInfo is dead.."));

            if (null != _imageRepository)
                Log.LogWrite(string.Format("Generation of _imageRepository is: {0}", GC.GetGeneration(_imageRepository)));
            else
                Log.LogWrite(string.Format("_imageRepository is dead.."));

            if (null != ScreenRecordingVideoArray)
                Log.LogWrite(string.Format("Generation of ScreenRecordingVideoArray is: {0}", GC.GetGeneration(ScreenRecordingVideoArray)));
            else
                Log.LogWrite(string.Format("ScreenRecordingVideoArray is dead.."));

        }

        /// <summary>
        /// Trying to resolve issue where Marshal.ReleaseComObject()
        /// called for ISOImage
        /// http://blogs.msdn.com/b/visualstudio/archive/2010/03/01/marshal-releasecomobject-considered-dangerous.aspx
        /// </summary>
        private static void CallGarbageCollection()
        {
            GC.Collect();
            GC.WaitForPendingFinalizers();

            Log.LogWrite(string.Format("Estimated amount of memory currently allocated on the managed heap: {0}", GC.GetTotalMemory(false).ToString("#,#")));
            Log.LogWrite(string.Format("Gen 0 has been swept {0} times...", GC.CollectionCount(0)));
            Log.LogWrite(string.Format("Gen 1 has been swept {0} times...", GC.CollectionCount(1)));
            Log.LogWrite(string.Format("Gen 2 has been swept {0} times...", GC.CollectionCount(2)));
        }

        /// <summary>
        /// now that we can have multiple eTimes,
        /// we will track the overall eTime...
        /// </summary>
        private void TotalElapsedTime()
        {
            _elapsedFileDownloadIsoCreationTime.Stop();
            _msgs = string.Format(RES.Resources.RES_TotalElapsedTime, FormatElapsedTime(_elapsedFileDownloadIsoCreationTime));
            PopulateStatusTextBox(_msgs, true);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="finished"></param>
        private void UpdateProgressBar(bool finished)
        {
            this.toolStripProgressBar.Style = ProgressBarStyle.Continuous;
            if (!finished)
            {
                for (int x = toolStripProgressBar.Value; x >= toolStripProgressBar.Minimum; Interlocked.Decrement(ref x))
                {
                    toolStripProgressBar.Value = x;
                    toolStripStatusLabel.Text = (this.toolStripProgressBar.Value / 2).ToString() + "%";
                }
            }
            else
            {
                toolStripProgressBar.Value = toolStripProgressBar.Maximum;
                toolStripStatusLabel.Text = (this.toolStripProgressBar.Value / 2).ToString() + RES.Resources.RES_PctISOImageCreationCompleted;
            }
        }

        /// <summary>
        /// persist any config page changes
        /// </summary>
        private void UpdateConfigSettings()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter UpdateConfigSettings()...");
            try
            {
                // global
                int tzIndex = 0; // valid default => (GMT-12:00) International Date Line West
                int.TryParse(ConfigurationManager.AppSettings["TZIndex"].ToString(), out tzIndex);


                // parameter page
                string userName = ConfigurationManager.AppSettings["UserName"];
                string startDate = ConfigurationManager.AppSettings.Get("StartDate");
                string endDate = ConfigurationManager.AppSettings["EndDate"];
                string archiveRecycleBin = ConfigurationManager.AppSettings["ArchiveRecycleBin"];
                string doYouWantToIncludeArchiveCalls = ConfigurationManager.AppSettings["IncludeArchivedCalls"];
                string outputLocation = ConfigurationManager.AppSettings["OutputLocation"];
                string mediaVolumeName = ConfigurationManager.AppSettings["MediaVolumeName"];

                // config page
                string isoDirectoryLayout = ConfigurationManager.AppSettings["ISODirectoryLayout"];
                string outputISOFileName = ConfigurationManager.AppSettings.Get("OutputISOFileName");
                string uxURL = ConfigurationManager.AppSettings["UXURL"];
                string arcURL = ConfigurationManager.AppSettings["ARCURL"];

                string createISO = ConfigurationManager.AppSettings["DoNotCreateISO"];
                string updateArchiveDbTables = ConfigurationManager.AppSettings["DoNotUpdateArchiveDbTables"];
                string doNotDownloadVideoFiles = ConfigurationManager.AppSettings["DoNotDownloadVideoFiles"];
                string saveDownloadedFiles = ConfigurationManager.AppSettings["SaveDownloadedFiles"];

                decimal maxNumberOfFilesToDownloadConcurrently = nudMultiFileDownload.Value; // valid default
                decimal.TryParse(ConfigurationManager.AppSettings["MaxNumberFilesToDownloadAtOnce"], out maxNumberOfFilesToDownloadConcurrently);

                decimal numberOfCPUs = nudNumberOfCPUs.Value; // valid default
                decimal.TryParse(ConfigurationManager.AppSettings["NumberOfCPUs"], out numberOfCPUs);

                decimal archiveNumberOfDaysLimit = 0;
                decimal.TryParse(ConfigurationManager.AppSettings["ArchiveNumberOfDaysLimit"], out archiveNumberOfDaysLimit);

                // viewer page
                string outputISOViewerLocation = ConfigurationManager.AppSettings["ISOViewerOutputLocation"];

                bool isModified = false;

                Configuration config =
                    ConfigurationManager.OpenExeConfiguration(
                    ConfigurationUserLevel.None);

                if (null != config)
                {
                    // global
                    if (comboBoxTimeZoneList.SelectedIndex != tzIndex)
                    {
                        config.AppSettings.Settings.Remove("TZIndex");
                        config.AppSettings.Settings.Add("TZIndex", comboBoxTimeZoneList.SelectedIndex.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("TZIndex: {0}"
                                , comboBoxTimeZoneList.SelectedIndex.ToString()));
                        Log.LogWrite(string.Format("TZName: {0}"
                            , comboBoxTimeZoneList.SelectedValue.ToString()));
                    }

                    //
                    // parameter tab contents
                    //
                    if (!txtUserName.Text.Equals(userName))
                    {
                        config.AppSettings.Settings.Remove("UserName");
                        config.AppSettings.Settings.Add("UserName", txtUserName.Text);
                        isModified = true;
                        Log.LogWrite(string.Format("UserName: {0}", txtUserName.Text));
                    }
                    dtpStartDate.Value = SetDate(dtpStartDate, dtpStartTime);
                    if (!dtpStartDate.Value.ToString().Equals(startDate))
                    {
                        config.AppSettings.Settings.Remove("StartDate");
                        config.AppSettings.Settings.Add("StartDate", dtpStartDate.Value.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("StartDate: {0}", dtpStartDate.Value.ToString()));
                    }
                    dtpEndDate.Value = SetDate(dtpEndDate, dtpEndTime);
                    if (!dtpEndDate.Value.ToString().Equals(endDate))
                    {
                        config.AppSettings.Settings.Remove("EndDate");
                        config.AppSettings.Settings.Add("EndDate", dtpEndDate.Value.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("EndDate: {0}", dtpEndDate.Value.ToString()));
                    }
                    if (!chkBoxArchiveRecylceBin.Checked.ToString().Equals(archiveRecycleBin))
                    {
                        config.AppSettings.Settings.Remove("ArchiveRecycleBin");
                        config.AppSettings.Settings.Add("ArchiveRecycleBin", chkBoxArchiveRecylceBin.Checked.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("ArchiveRecycleBin: {0}", chkBoxArchiveRecylceBin.Checked.ToString()));
                    }
                    if (!chkBoxIncludeArchivedCalls.Checked.ToString().Equals(archiveRecycleBin))
                    {
                        config.AppSettings.Settings.Remove("IncludeArchivedCalls");
                        config.AppSettings.Settings.Add("IncludeArchivedCalls", chkBoxIncludeArchivedCalls.Checked.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("IncludeArchivedCalls: {0}", chkBoxIncludeArchivedCalls.Checked.ToString()));
                    }
                    if (!txtOutputLocation.Text.Equals(outputLocation))
                    {
                        config.AppSettings.Settings.Remove("OutputLocation");
                        config.AppSettings.Settings.Add("OutputLocation", txtOutputLocation.Text);
                        isModified = true;
                        Log.LogWrite(string.Format("OutputLocation: {0}", txtOutputLocation.Text));
                    }
                    if (!txtMediaVolumeName.Text.Equals(mediaVolumeName))
                    {
                        config.AppSettings.Settings.Remove("MediaVolumeName");
                        config.AppSettings.Settings.Add("MediaVolumeName", txtMediaVolumeName.Text);
                        isModified = true;
                        Log.LogWrite(string.Format("MediaVolumeName: {0}", txtMediaVolumeName.Text));
                    }
                    if (_archiveNumberOfDaysLimit != archiveNumberOfDaysLimit)
                    {
                        config.AppSettings.Settings.Remove("ArchiveNumberOfDaysLimit");
                        config.AppSettings.Settings.Add("ArchiveNumberOfDaysLimit", _archiveNumberOfDaysLimit.ToString(CultureInfo.InvariantCulture));
                        isModified = true;
                        Log.LogWrite(string.Format("ArchiveNumberOfDaysLimit: {0}", txtMediaVolumeName.Text));
                    }

                    //
                    // config tab contents
                    //
                    if (!txtISODirectoryLayout.Text.Equals(isoDirectoryLayout))
                    {
                        config.AppSettings.Settings.Remove("ISODirectoryLayout");
                        config.AppSettings.Settings.Add("ISODirectoryLayout", txtISODirectoryLayout.Text);
                        isModified = true;
                        Log.LogWrite(string.Format("ISODirectoryLayout: {0}", txtISODirectoryLayout.Text));
                    }
                    if (!txtCustomFileName.Text.Equals(outputISOFileName))
                    {
                        config.AppSettings.Settings.Remove("OutputISOFileName");
                        config.AppSettings.Settings.Add("OutputISOFileName", txtCustomFileName.Text);
                        isModified = true;
                        Log.LogWrite(string.Format("OutputISOFileName: {0}", txtCustomFileName.Text));
                    }
                    /*
                    if (!txtUXURL.Text.Equals(uxURL))
                    {
                        config.AppSettings.Settings.Remove("UXURL");
                        config.AppSettings.Settings.Add("UXURL", txtUXURL.Text);
                        isModified = true;
                        Log.LogWrite(string.Format("UXURL: {0}", txtUXURL.Text));
                    }
                     */
                    if (!txtWebServiceURL.Text.Equals(arcURL))
                    {
                        config.AppSettings.Settings.Remove("ARCURL");
                        config.AppSettings.Settings.Add("ARCURL", txtWebServiceURL.Text);
                        isModified = true;
                        Log.LogWrite(string.Format("ARCURL: {0}", txtWebServiceURL.Text));
                    }
                    if (!chkBoxDoNotCreateISOImage.Checked.ToString().Equals(createISO))
                    {
                        config.AppSettings.Settings.Remove("DoNotCreateISO");
                        config.AppSettings.Settings.Add("DoNotCreateISO", chkBoxDoNotCreateISOImage.Checked.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("DoNotCreateISO: {0}", chkBoxDoNotCreateISOImage.Checked.ToString()));
                    }
                    if (!chkBoxDoNotUpdateArchiveTables.Checked.ToString().Equals(updateArchiveDbTables))
                    {
                        config.AppSettings.Settings.Remove("DoNotUpdateArchiveDbTables");
                        config.AppSettings.Settings.Add("DoNotUpdateArchiveDbTables", chkBoxDoNotUpdateArchiveTables.Checked.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("DoNotUpdateArchiveDbTables: {0}", chkBoxDoNotUpdateArchiveTables.Checked.ToString()));
                    }
                    if (!chkBoxDoNotDownloadVideoFiles.Checked.ToString().Equals(doNotDownloadVideoFiles))
                    {
                        config.AppSettings.Settings.Remove("DoNotDownloadVideoFiles");
                        config.AppSettings.Settings.Add("DoNotDownloadVideoFiles", chkBoxDoNotDownloadVideoFiles.Checked.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("DoNotDownloadVideoFiles: {0}", chkBoxDoNotDownloadVideoFiles.Checked.ToString()));
                    }
                    if (!chkBoxDoNotDeleteDownloadedFiles.Checked.ToString().Equals(saveDownloadedFiles))
                    {
                        config.AppSettings.Settings.Remove("SaveDownloadedFiles");
                        config.AppSettings.Settings.Add("SaveDownloadedFiles", chkBoxDoNotDeleteDownloadedFiles.Checked.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("SaveDownloadedFiles: {0}", chkBoxDoNotDeleteDownloadedFiles.Checked.ToString()));
                    }
                    if (nudMultiFileDownload.Value != maxNumberOfFilesToDownloadConcurrently)
                    {
                        config.AppSettings.Settings.Remove("MaxNumberFilesToDownloadAtOnce");
                        config.AppSettings.Settings.Add("MaxNumberFilesToDownloadAtOnce", nudMultiFileDownload.Value.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("MaxNumberFilesToDownloadAtOnce: {0}", nudMultiFileDownload.Value.ToString()));
                    }
                    if (nudNumberOfCPUs.Value != numberOfCPUs)
                    {
                        config.AppSettings.Settings.Remove("NumberOfCPUs");
                        config.AppSettings.Settings.Add("NumberOfCPUs", nudNumberOfCPUs.Value.ToString());
                        isModified = true;
                        Log.LogWrite(string.Format("NumberOfCPUs: {0}", nudNumberOfCPUs.Value.ToString()));
                    }

                    //
                    // viewer tab contents
                    //
                    if (!txtISOFileReaderOutputDir.Text.Equals(outputISOViewerLocation))
                    {
                        config.AppSettings.Settings.Remove("ISOViewerOutputLocation");
                        config.AppSettings.Settings.Add("ISOViewerOutputLocation", txtISOFileReaderOutputDir.Text);
                        isModified = true;
                        Log.LogWrite(string.Format("ISOViewerOutputLocation: {0}", txtISOFileReaderOutputDir.Text));
                    }

                    //
                    // pages have been evaluated - 
                    // if any modifications found take care of it...
                    //
                    if (isModified)
                    {
                        config.Save(ConfigurationSaveMode.Modified);
                        // Refresh the appSettings section so the secction
                        // is read from the disk and not from the cache when
                        // requested, next time.                    
                        ConfigurationManager.RefreshSection("AppSettings");
                    }
                }
            }
            catch (Exception ex)
            {
                Log.LogWrite(ErrorMessageString(ex));
            }
            finally
            {
                Log.LogWrite("Exit UpdateConfigSettings()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// loads the index content for
        /// the selected iso into the viewer
        /// </summary>
        private void UpdateViewerContent()
        {
            txtISOFile.Text = txtOutputLocation.Text;
            if (btnISOFileLoad.Enabled)
            {
                btnISOFileLoad_Click(this, null);
            }
        }

        /// <summary>
        /// this was added to support creating
        /// multiple index files for each
        /// iso image we generate...
        /// </summary>
        /// <param name="listIndexData"></param>
        /// <param name="indexName"></param>
        private void CreateArchiveIndexFile(List<FileImageInfo.IndexData> listIndexData
            , string indexName)
        {
            CreateCSVFile(listIndexData, indexName);
        }

        ////////////////////////////////////////////////////////////////////////// 
        #endregion

        #region Database Update...
        //////////////////////////////////////////////////////////////////////////
        /// <summary>
        /// Call web service to add
        /// calls to archive table(s)
        /// </summary>
        private void UpdateTables()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter UpdateTables()...");
            try
            {
                int archiveID = UpdateArchiveTable();
                if (-1 != archiveID)
                {
                    UpdateArchiveLinkTable(archiveID);
                }
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                UpdateEventViewer(_msgs, EventLogEntryType.Error);
            }
            finally
            {
                Log.LogWrite("Exit UpdateTables()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// populate the archive table with the name of
        /// this ISO image file
        /// </summary>
        /// <returns></returns>
        private int UpdateArchiveTable()
        {
            int attempts = 0;
            bool done = false;
            int archiveID = -1;

            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter UpdateArchiveTable()...");
            try
            {
                while (!done && attempts < _maxAttemptsToContactServer)
                {
                    var classicArchiveWS = ClassicArchiveWS;

                    try
                    {
                        Interlocked.Increment(ref attempts);

                        archiveID = classicArchiveWS.AddArchive(
                            ObjFileImageInfo.UserName
                            , ObjFileImageInfo.PassWord
                            , new FileInfo(ObjFileImageInfo.ArchiveFileName).CreationTime.ToUniversalTime()
                            , ObjFileImageInfo.ArchiveFileName
                            , ObjFileImageInfo.ItemCount
                            , ComputeMD5Hash(ObjFileImageInfo.ArchiveFileName)
                            , ObjFileImageInfo.IsAdmin);

                        done = true;
                        _msgs = string.Format(RES.Resources.RES_UpdateOfArchiveTableSucceeded, attempts);
                        PopulateStatusTextBox(_msgs, true);
                    }
                    catch (Exception e)
                    {
                        #region error...
                        _msgs = string.Format(RES.Resources.RES_UpdateOfArchiveTableFailed
                            , e.Message
                            , attempts
                            , _maxAttemptsToContactServer);
                        PopulateStatusTextBox(_msgs, true);

                        _msgs = string.Format(RES.Resources.RES_UpdateOfArchiveTableFailedEventViewer
                                    , e.Message
                                    , e.InnerException
                                    , e.StackTrace);
                        UpdateEventViewer(_msgs, EventLogEntryType.Error);

                        if (attempts >= _maxAttemptsToContactServer)
                            throw new SRIPArchiveClientFormException(_msgs);
                        else
                            Thread.Sleep(OneSecond);
                        #endregion
                    }
                }
            }
            finally
            {
                Log.LogWrite("Exit UpdateArchiveTable()... " + FormatElapsedTime(stopwatch));
            }

            return archiveID;
        }

        /// <summary>        
        /// poulates the link table with the 
        /// archive ID and the corresponding
        /// call ID's that were selected
        /// TODO: Need to update Archives.cs
        /// to include a RecordingID property...
        /// </summary>
        /// <param name="archiveID"></param>
        private void UpdateArchiveLinkTable(int archiveID)
        {
            int attempts = 0;
            bool done = false;

            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter UpdateArchiveLinkTable()...");
            Log.LogWrite("New ArchiveID: " + archiveID);
            try
            {

                while (!done && attempts < ChunkRetryLimit)
                {
                    var classicArchiveWS = ClassicArchiveWS;

                    try
                    {
                        Interlocked.Increment(ref attempts);
                        //
                        //ArchiveData[] convertToWebServiceArchiveDataObj = ObjFileImageInfo.ArchiveTableList.ConvertAll
                        //    (i => new ArchiveData()
                        //          {
                        //              CallId = i.CallId
                        //              ,
                        //              ScrRecordingID =
                        //                  i.ScrRecordingID.Equals(-1)
                        //                      ? null
                        //                      : i.ScrRecordingID
                        //          }).ToArray();

                        //wsSoapClient.UpdateArchiveLinkTable(ObjFileImageInfo.UserName
                        //    , ObjFileImageInfo.PassWord
                        //    , archiveID
                        //    , convertToWebServiceArchiveDataObj);


                        // 
                        // Case #123278: Update of archive link table failed – per the error message 
                        //               a timeout occurred during the operation
                        //
                        // Changing update process to send one record at a time...
                        //
                        ObjFileImageInfo.ArchiveTableList.ForEach
                        (ad => classicArchiveWS.UpdateArchiveLinkTable(
                                ObjFileImageInfo.UserName
                                , ObjFileImageInfo.PassWord
                                , archiveID
                                , new[]
                                {
                                    new ArchiveData()
                                    {
                                        CallId = ad.CallId,
                                        ScrRecordingID = ad.ScrRecordingID.Equals(-1) ? null : ad.ScrRecordingID
                                    }
                                }));

                        done = true;

                        _msgs = string.Format(RES.Resources.RES_UpdateOfArchiveLinkTableSucceeded, attempts);
                        PopulateStatusTextBox(_msgs, true);
                    }
                    catch (Exception e)
                    {
                        #region error...
                        _msgs = string.Format(RES.Resources.RES_UpdateOfArchiveLinkTableFailed
                            , e.Message
                            , attempts
                            , _maxAttemptsToContactServer);
                        PopulateStatusTextBox(_msgs, true);

                        _msgs = string.Format(RES.Resources.RES_UpdateOfArchiveLinkTableFailedEventViewer
                                    , e.Message
                                    , e.InnerException
                                    , e.StackTrace);
                        UpdateEventViewer(_msgs, EventLogEntryType.Error);

                        if (attempts >= _maxAttemptsToContactServer)
                            throw new SRIPArchiveClientFormException(_msgs);
                        else
                            Thread.Sleep(ChunkRetryWaitTimeInMilliseconds);
                        #endregion
                    }
                }
            }
            finally
            {
                Log.LogWrite("Exit UpdateArchiveLinkTable()... " + FormatElapsedTime(stopwatch));
            }
        }
        //////////////////////////////////////////////////////////////////////////
        #endregion

        #region Generic Utilities...
        //////////////////////////////////////////////////////////////////////////

        /// <summary>
        /// TODO: Need to localize the buttons...
        /// </summary>
        private void LocalizeUIItems()
        {
            RES.Resources.Culture = CultureInfo.CurrentCulture;

            btnISOFileLoad.Text = RES.Resources.RES_BTN_Load;
            btnCreateOutputFile.Text = RES.Resources.RES_BTN_Create;
            btnCopyText.Text = RES.Resources.RES_BTN_CopyStatusText;

            btnSaveLocation.Text =
            btnISOReaderOutputDir.Text =
            btnISOFileBrowse.Text = RES.Resources.RES_BTN_Browse;

            lblUserName.Text = RES.Resources.RES_LBL_UserName;
            lblPassword.Text = RES.Resources.RES_LBL_Password;
            lblStartDate.Text = RES.Resources.RES_LBL_StartDate;
            lblEndDate.Text = RES.Resources.RES_LBL_EndDate;
            lblLocation.Text = RES.Resources.RES_LBL_OutputDirectory;
            lblMediaVolumeName.Text = RES.Resources.RES_LBL_VolumeName;
            lblWebServiceURL.Text = RES.Resources.RES_LBL_CallRecordingURL;
            lblISOFileStructure.Text = RES.Resources.RES_LBL_ISODirectoryLayout;
            //lblISOFileStructure.Text = Resources.SRIPArchiveClientForm_LocalizeUIItems_Work_Directory;
            lblCustomFileName.Text = RES.Resources.RES_LBL_CustomFileName;
            lblISOFileReaderInput.Text = RES.Resources.RES_LBL_Input;
            lblISOFileReaderOutput.Text = RES.Resources.RES_LBL_Output;
            lblTimeZone.Text = RES.Resources.RES_LBL_TimeZone;

            tabControlISOWriter.TabPages[0].Text = RES.Resources.RES_TAB_Parameters;
            tabControlISOWriter.TabPages[1].Text = RES.Resources.RES_TAB_Configuration;
            tabControlISOWriter.TabPages[2].Text = RES.Resources.RES_TAB_Viewer;

            grpBoxAuthenticate.Text = RES.Resources.RES_GRP_Authenticate;
            grpBoxImageDetails.Text = RES.Resources.RES_GRP_ImageDetails;
            grpDateRange.Text = RES.Resources.RES_GRP_SearchCriteria;
            grpBoxSettings.Text = RES.Resources.RES_GRP_Settings;
            grpBoxStatus.Text = RES.Resources.RES_GRP_Status;
            grpBoxISOFile.Text = RES.Resources.RES_GRP_ISOFile;

            toolStripLabelSearchText.Text = RES.Resources.RES_LBL_Search;
            toolStripLabelSearchCriteria.Text = RES.Resources.RES_LBL_For;

            chkBoxDoNotDownloadVideoFiles.Text = RES.Resources.RES_CHKBOX_DoNotDownloadVideoFiles;
            chkBoxDoNotCreateISOImage.Text = RES.Resources.RES_CHKBOX_DoNotCreateISOImage;
            chkBoxDoNotUpdateArchiveTables.Text = RES.Resources.RES_CHKBOX_DoNotUpdateArchiveDatabaseTables;
            chkBoxDoNotDeleteDownloadedFiles.Text = RES.Resources.RES_CHKBOX_DoNotDeleteDownloadedWorkFiles;
            chkBoxArchiveRecylceBin.Text = RES.Resources.RES_CHKBOX_ArchiveContentsOfRecycleBin;
            chkBoxIncludeArchivedCalls.Text = RES.Resources.RES_CHKBOX_IncludeArchivedCalls;

            lblNrOfFilesDownloaded.Text = RES.Resources.RES_LBL_DownloadFilesConcurrently;
            lblNrOfCPUs.Text = RES.Resources.RES_NUD_NumberOfCPUs;
            lblNrOfConnections.Text = RES.Resources.RES_NUD_NumberOfConnections;
        }

        /// <summary>
        /// TODO: Need to add columns for video link...
        /// </summary>
        private void AddGridviewFilterSupport()
        {
            if (this.SearchFieldData == null) this.SearchFieldData = new List<SearchField>();

            int index = 0;
            for (int x = 0; x < _dgISOContentView.Columns.Count; Interlocked.Increment(ref x))
            {
                string dataPropertyName = _dgISOContentView.Columns[x].DataPropertyName;
                string headerText = _dgISOContentView.Columns[x].HeaderText;

                // hack - just ignore some columns
                if (dataPropertyName.Equals("LocLookupDisplay")) continue;
                if (dataPropertyName.Equals("UploadCall")) continue;
                if (dataPropertyName.Equals("Duration")) continue;
                if (dataPropertyName.Equals("DiskSize")) continue;
                if (dataPropertyName.Equals("Md5Hash")) continue;
                if (dataPropertyName.Equals("UserName")) continue;

                SearchFieldData.Add(new SearchField
                {
                    DataPropertyName = dataPropertyName
                     ,
                    FriendlyName = headerText
                     ,
                    Index = index
                });

                Interlocked.Increment(ref index);
            }

            foreach (SearchField s in SearchFieldData) toolStripComboBoxColumnNames.Items.Add(s.FriendlyName);
            toolStripComboBoxColumnNames.SelectedIndex = 0;
            //toolStripTextBoxFilter.Enabled = false;
        }

        /// <summary>
        /// 
        /// </summary>
        private void RemoveTempDir()
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter RemoveTempDir()...");
            try
            {
                if (_safeToDeleteTempDirectory && _doNotDeleteDownloadedFiles.Equals(false))
                {
                    string isoDirectoryLayout = new FileInfo(txtISODirectoryLayout.Text).DirectoryName;
                    if (isoDirectoryLayout != null)
                    {
                        var dirInfo = new DirectoryInfo(isoDirectoryLayout);
                        if (dirInfo.Exists)
                        {
                            try
                            {
                                lock (_writeIndexContentLock)
                                {
                                    DeleteFolder(dirInfo);
                                }
                            }
                            catch (Exception ex)
                            {
                                _msgs = ErrorMessageString(ex);
                                Log.LogWrite("1. RemoveTempDir Error: " + _msgs);
                            }
                        }
                    }
                }
                _safeToDeleteTempDirectory = false;
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                Log.LogWrite("2. RemoveTempDir error: " + _msgs);
            }
            finally
            {
                Log.LogWrite("Exit RemoveTempDir()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// help u remove dir...
        /// </summary>
        /// <param name="di"></param>
        private void DeleteFolder(DirectoryInfo di)
        {
            foreach (DirectoryInfo dif in di.GetDirectories())
            {
                dif.Attributes = FileAttributes.Normal;
                DeleteFolder(dif);
            }
            foreach (FileInfo fi in di.GetFiles())
            {
                fi.Attributes = FileAttributes.Normal;
                //
                // bug fix - only delete the files we know about...
                //
                if (ObjFileImageInfo.PathsAndFileNames.Contains(fi.FullName) ||
                    fi.FullName.Contains(Resources.RES_IndexCSVFileName))
                {
                    try
                    {
                        fi.Delete();
                    }
                    catch (Exception ex) { Log.LogWrite("Warning: " + ex.Message); }
                }
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="msg"></param>
        /// <param name="append"></param>
        public bool PopulateStatusTextBox(string msg, bool append)
        {

            if (this.InvokeRequired)
            {
                string m = string.Format("Caller does not have access to this control. Desired to post the following text: {0}", msg);
                UpdateEventViewer((m.Replace("\\r\\n", "\r\n") + "\r\n"), EventLogEntryType.Warning);
                return false;
            }

            txtBoxStatus.Text = append ? txtBoxStatus.Text +=
                (msg.Replace("\\r\\n", "\r\n") + "\r\n") :
                (msg + "\r\n");

            Log.LogWrite("PopulateStatusTextBox(): " + (msg.Replace("\\r\\n", "\r\n")));

            txtBoxStatus.SelectionStart = txtBoxStatus.Text.Length;
            txtBoxStatus.ScrollToCaret();

            return true;
        }

        /// <summary>
        /// 
        /// </summary>
        private void RestoreWindow()
        {
            try
            {
                if (Properties.Settings.Default.WindowHeight == 0 ||
                    Properties.Settings.Default.WindowWidth == 0)
                {
                    return;
                }
                this.Height = Properties.Settings.Default.WindowHeight;
                this.Width = Properties.Settings.Default.WindowWidth;
                Point windowPoint = new Point(Properties.Settings.Default.WindowLocationX
                    , Properties.Settings.Default.WindowLocationY);
                //
                //  annoying bug: if a user minimizes this application
                //  and closes the application while it's minimized
                //  in the taskbar, the saved values for X and Y 
                //  will be less than 0 - and if we restore the
                //  window with these coordinates, the location 
                //  will be not be visible to the user and they will
                //  have no way to bring the application back on the desktop...
                //
                this.Location = ((windowPoint.X > -1) && (windowPoint.Y > -1))
                    ? windowPoint
                    : this.Location;
                this.StartPosition = FormStartPosition.Manual;
                if (Properties.Settings.Default.WindowState == "Normal")
                {
                    this.WindowState = FormWindowState.Normal;
                }
                else if (Properties.Settings.Default.WindowState == "Maximized")
                {
                    this.WindowState = FormWindowState.Maximized;
                }
                //_msgs = string.Format("Window position restore:\r\nHeight: {0}\r\nWidth: {1}\r\nLocationX: {2}\r\nLocationY: {3}\r\nWindowState: {4}"
                //    , this.Height.ToString()
                //    , this.Width.ToString()
                //    , this.Location.X.ToString()
                //    , this.Location.Y.ToString()
                //    , this.WindowState.ToString());
                //UpdateEventViewer(_msgs, EventLogEntryType.Information);

                Log.LogWrite("Window Position Restore:");
                Log.LogWrite("Height: " + this.Height);
                Log.LogWrite("Width: " + this.Width);
                Log.LogWrite("LocationX: " + this.Location.X);
                Log.LogWrite("LocationY: " + this.Location.Y);
                Log.LogWrite("WindowState: " + this.WindowState);


            }
            catch (Exception ex)
            {
                _msgs = string.Format("Error during window position restore: {0}"
                    , ex.Message);
                UpdateEventViewer(_msgs, EventLogEntryType.Information);
            }
        }

        /// <summary>
        /// try guessing how much longer 
        /// this will take to download the selected file(s)...
        /// </summary>
        /// <param name="totalTasks"></param>
        /// <param name="completedTasks"></param>
        /// <returns></returns>
        private string TimeRemainingEstimate(int totalTasks, int completedTasks)
        {
            var secondsremaining = (double)((_timeRemainingEstimates.Elapsed.TotalSeconds / completedTasks) * (totalTasks - completedTasks));
            var ts = TimeSpan.FromSeconds(secondsremaining);// new TimeSpan(0, 0, (int)secondsremaining);
            return FormatElapsedTime(ts);
        }

        private string TimeRemainingEstimate(int totalTasks, int completedTasks, Stopwatch timer)
        {
            var secondsremaining = (double)((timer.Elapsed.TotalSeconds / completedTasks) * (totalTasks - completedTasks));
            var ts = TimeSpan.FromSeconds(secondsremaining);// new TimeSpan(0, 0, (int)secondsremaining);
            return FormatElapsedTime(ts);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="ts"></param>
        /// <returns></returns>
        private string FormatElapsedTime(TimeSpan ts)
        {
            //
            // Add code to handle when the 
            // elapsed time is greater than 24 hours...
            //
            var hours = ts.Days > 0 ? ts.Days * 24 + ts.Hours : ts.Hours;
            return string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                    , hours
                    , ts.Minutes
                    , ts.Seconds
                    , ts.Milliseconds / 10);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="dtpDate"></param>
        /// <param name="dtpTime"></param>
        /// <returns></returns>
        private DateTime SetDate(DateTimePicker dtpDate, DateTimePicker dtpTime)
        {
            return new DateTime(dtpDate.Value.Year
                , dtpDate.Value.Month
                , dtpDate.Value.Day
                , dtpTime.Value.Hour
                , dtpTime.Value.Minute
                , dtpTime.Value.Second);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="stopwatch"></param>
        /// <returns></returns>
        private string FormatElapsedTime(Stopwatch stopwatch)
        {
            var ts = stopwatch.Elapsed;
            //
            // Add code to handle when the 
            // elapsed time is greater than 24 hours...
            //
            var hours = ts.Days > 0 ? ts.Days * 24 + ts.Hours : ts.Hours;
            return string.Format("{0:00}:{1:00}:{2:00}.{3:0000}"
                    , hours
                    , ts.Minutes
                    , ts.Seconds
                    , ts.Milliseconds / 10);
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="sDevice"></param>
        private void VerifyTempFolderFreeSpaceAcceptableForSelectedFileImage(string sDevice)
        {
            ManagementObject disk = new ManagementObject(sDevice);
            disk.Get();
            _hdSize = long.Parse(disk["Size"].ToString());
            _freeSpace = long.Parse(disk["FreeSpace"].ToString());

            if ((_imageRepository.SizeBeforeFormatting * 2) > _freeSpace)
            {
                _msgs = string.Format(RES.Resources.RES_RequestCancelDriveWhereTempFolderLocatedDoesNotHaveEnoughSpace
                    , "Drive: " + sDevice + " " + (_imageRepository.SizeBeforeFormatting * 2).ToString("#,#")
                    , _freeSpace.ToString("#,#"));
                UpdateEventViewer(_msgs);
                throw new SRIPArchiveClientFormException(_msgs);
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="list"></param>
        private void CreateCSVFile(List<FileImageInfo.IndexData> list, string indexName)
        {
            if (null != list && list.Count > 0)
            {
                string fileName = new FileInfo(_isoDirectoryLayout).DirectoryName + '\\' + indexName;

                var sbCSVFile = new StringBuilder();
                string csvFileContent;

                var needHeader = true;
                foreach (FileImageInfo.IndexData id in list)
                {
                    if (needHeader)
                    {
                        #region CSV Header...
                        csvFileContent = string.Empty;
                        csvFileContent += string.Format("\"{0}\",", "UserName");
                        csvFileContent += string.Format("\"{0}\",", "ExtnNumber");
                        csvFileContent += string.Format("\"{0}\",", "CallID");
                        csvFileContent += string.Format("\"{0}\",", "CallDateTime");
                        csvFileContent += string.Format("\"{0}\",", "FromNumber");
                        csvFileContent += string.Format("\"{0}\",", "ToNumber");
                        csvFileContent += string.Format("\"{0}\",", "Duration");
                        csvFileContent += string.Format("\"{0}\",", "DiskSize");
                        csvFileContent += string.Format("\"{0}\",", "Location");
                        csvFileContent += string.Format("\"{0}\",", "Comments");
                        csvFileContent += string.Format("\"{0}\",", "ExtensionId");
                        csvFileContent += string.Format("\"{0}\",", "Md5Hash");
                        csvFileContent += string.Format("\"{0}\",", "RecordedFileName");
                        csvFileContent += string.Format("\"{0}\",", "FromCallerID");
                        csvFileContent += string.Format("\"{0}\",", "ToCallerID");
                        csvFileContent += string.Format("\"{0}\",", "DirectionFlag");
                        csvFileContent += string.Format("\"{0}\",", "LocLookupDisplay");
                        csvFileContent += string.Format("\"{0}\",", "UploadCall");
                        csvFileContent += string.Format("\"{0}\",", "VolumeName"); //Bug #3602: show vol name on viewer page

                        // start: added for video recordings...                        
                        csvFileContent += string.Format("\"{0}\",", "RecordingId");
                        csvFileContent += string.Format("\"{0}\",", "RecordingGuid");
                        csvFileContent += string.Format("\"{0}\",", "VideoFileName");
                        csvFileContent += string.Format("\"{0}\",", "AudioPosition");
                        csvFileContent += string.Format("\"{0}\",", "StartPos");
                        csvFileContent += string.Format("\"{0}\",", "EndPos");
                        // end: added for video recordings...

                        sbCSVFile.AppendLine(csvFileContent);
                        needHeader = false;
                        #endregion
                    }

                    #region CSV Detail...
                    csvFileContent = string.Empty;
                    csvFileContent += string.Format("\"{0}\",", id.UserName);
                    csvFileContent += string.Format("\"{0}\",", id.ExtnNumber);
                    csvFileContent += string.Format("\"{0}\",", id.CallID);
                    csvFileContent += string.Format("\"{0}\",", id.CallDateTime.Ticks); // include ms in time...
                    csvFileContent += string.Format("\"{0}\",", id.FromNumber);
                    csvFileContent += string.Format("\"{0}\",", id.ToNumber);
                    csvFileContent += string.Format("\"{0}\",", id.Duration);
                    csvFileContent += string.Format("\"{0}\",", id.DiskSize);
                    csvFileContent += string.Format("\"{0}\",", id.Location);
                    csvFileContent += string.Format("\"{0}\",", ConvertWhitespaceToSpacesRegex(id.Comments));
                    csvFileContent += string.Format("\"{0}\",", id.ExtensionId);
                    csvFileContent += string.Format("\"{0}\",", id.Md5Hash);
                    csvFileContent += string.Format("\"{0}\",", new FileInfo(id.RecordedFileName).Name);
                    csvFileContent += string.Format("\"{0}\",", id.FromCallerID);
                    csvFileContent += string.Format("\"{0}\",", id.ToCallerID);
                    csvFileContent += string.Format("\"{0}\",", id.DirectionFlag);
                    csvFileContent += string.Format("\"{0}\",", id.LocLookupDisplay);
                    csvFileContent += string.Format("\"{0}\",", id.Selected);
                    csvFileContent += string.Format("\"{0}\",", _mediaVolumeName); //Bug #3602: show vol name on viewer page

                    // start: added for video recordings...
                    csvFileContent += string.Format("\"{0}\",", id.RecordingId);
                    csvFileContent += string.Format("\"{0}\",", id.RecordingGuid);

                    if (!_doNotDownloadVideoFiles && !string.IsNullOrEmpty(id.VideoFileName))
                        csvFileContent += string.Format("\"{0}\",", new FileInfo(id.VideoFileName).Name);
                    else
                        csvFileContent += string.Format("\"{0}\",", string.Empty);

                    csvFileContent += string.Format("\"{0}\",", id.AudioPosition);
                    csvFileContent += string.Format("\"{0}\",", id.StartPos);
                    csvFileContent += string.Format("\"{0}\",", id.EndPos);
                    // end: added for video recordings...

                    sbCSVFile.AppendLine(csvFileContent);
                    #endregion
                }
                WriteFileOut(fileName, sbCSVFile.ToString());
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="value"></param>
        /// <returns></returns>
        private static string ConvertWhitespaceToSpacesRegex(string value)
        {
            const string pattern = "\\s+";
            const string replacement = " ";
            value = Regex.Replace(value, pattern, replacement);
            return value;
        }

        /// <summary>
        /// file writer
        /// </summary>
        /// <param name="fileName"></param>
        /// <param name="msg"></param>
        private static void WriteFileOut(string fileName, string msg)
        {
            var success = true;
            Log.LogWrite("Attempting to create: " + fileName);
            try
            {
                lock (_writeIndexContentLock)
                {
                    try
                    {
                        using (var streamWriter = new StreamWriter(fileName))
                        {
                            streamWriter.WriteLine(msg);
                            streamWriter.Flush();
                        }
                    }
                    catch (Exception ex)
                    {
                        success = false;
                        Log.LogWrite("WriteFileOut(StreamWriter) Error: " + ex.Message);
                        throw new SRIPArchiveClientFormException(ex.Message);
                    }
                }
            }
            finally
            {
                if (success)
                    Log.LogWrite("Succeeded creating: " + fileName);
                else
                    Log.LogWrite("Unable to create: " + fileName);
            }
        }

        /// <summary>
        /// Exception details...
        /// </summary>
        /// <param name="ex"></param>
        /// <returns></returns>
        private static string ErrorMessageString(Exception ex)
        {
            var sb = new StringBuilder();
            try
            {
                sb.Append(string.Format("Exception Message: {0}\r\n" +
                       "Member name: {1}\r\n" +
                       "Member type: {2}\r\n" +
                       "Source: {3}\r\n" +
                       "Class defining member: {4}\r\n" +
                       "StackTrace: {5}",
                      ex.Message
                    , ex.TargetSite
                    , ex.TargetSite.MemberType
                    , string.IsNullOrEmpty(ex.Source) ? "N/A" : ex.Source
                    , ex.TargetSite.DeclaringType
                    , string.IsNullOrEmpty(ex.StackTrace) ? "N/A" : ex.StackTrace));
            }
            catch { }
            return sb.ToString();
        }

        /// <summary>
        /// 
        /// </summary>
        private static void WriteTransportErrorsToEventViewer()
        {
            foreach (var msgs in _transportErrors
                .Select(s => string.Format("Transport Error: " + s)))
            {
                UpdateEventViewer(msgs, EventLogEntryType.Warning);
            }
        }

        /// <summary>
        /// 
        /// </summary>
        private void StartMovie(string movieFile)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter StartMovie()...");
            try
            {
                //using (Process p = new Process())
                Process p = new Process();
                p.StartInfo.FileName = movieFile;
                p.StartInfo.UseShellExecute = true;
                p.StartInfo.CreateNoWindow = true;
                p.StartInfo.WorkingDirectory = new FileInfo(Application.ExecutablePath).DirectoryName;
                ThreadPool.QueueUserWorkItem(StartVideoPlayer, p);
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                Log.LogWrite(_msgs);
            }
            finally
            {
                Log.LogWrite("Exit StartMovie()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="proc"></param>
        private void StartVideoPlayer(object proc)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter StartVideoPlayer()...");
            try
            {
                using (Process obj = proc as Process)
                {
                    if (obj.Start())
                    {
                        obj.WaitForExit();
                        int exitcode = obj.ExitCode;
                        Log.LogWrite(@"Exit code: " + exitcode);
                    }
                }
            }
            finally
            {
                Log.LogWrite("Exit StartVideoPlayer()... " + FormatElapsedTime(stopwatch));
                _autoEventLoadAudioVideoFileInGrid.Set();
            }
        }

        ////////////////////////////////////////////////////////////////////////// 
        #endregion

        #region Event Log Utilities...
        //////////////////////////////////////////////////////////////////////////        
        /// <summary>
        /// 
        /// </summary>
        /// <param name="eventMsg"></param>
        private static void UpdateEventViewer(string eventMsg)
        {
            try
            {
                if (EventLog.SourceExists(_appName))
                    EventLog.WriteEntry(_appName, eventMsg);
            }
            catch { /*no event log here...*/ }
            finally { Log.LogWrite(eventMsg); }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <param name="eventMsg"></param>
        /// <param name="logEntryType"></param>
        private static void UpdateEventViewer(string eventMsg, EventLogEntryType logEntryType)
        {
            try
            {
                if (EventLog.SourceExists(_appName))
                    EventLog.WriteEntry(_appName, eventMsg, logEntryType);

                if (EventLogEntryType.Error.Equals(logEntryType))
                {
                    string callStackFrame;
                    string callStackDetails;
                    GetDetailStackTraceInfo(out callStackFrame, out callStackDetails);

                    eventMsg += ("\r\n" + callStackFrame + "\r\n" + callStackDetails);

                }
            }
            catch { /*no event log here...*/ }
            finally { Log.LogWrite(eventMsg); }
        }

        /// <summary>
        /// additional stack trace detail...
        /// </summary>
        /// <param name="callStackFrame"></param>
        /// <param name="callStackDetails"></param>
        private static void GetDetailStackTraceInfo(out string callStackFrame, out string callStackDetails)
        {
            StackTrace s = new StackTrace(true);

            callStackFrame = string.Format("Total frames: {0}\r\nCurrent method: {1}\r\nCalling method: {2}"
                , s.FrameCount
                , s.GetFrame(0).GetMethod().Name
                , s.GetFrame(1).GetMethod().Name);

            callStackDetails = string.Empty;
            foreach (StackFrame sf in s.GetFrames())
            {
                if (null == sf) continue;
                if (string.IsNullOrEmpty(sf.GetFileName())) continue;

                callStackDetails +=
                                "FN: " + sf.GetFileName() + "\r\n" +
                                "FLN: " + sf.GetFileLineNumber() + "\r\n" +
                                "FCN: " + sf.GetFileColumnNumber() + "\r\n" +
                                "Method: " + sf.GetMethod().Name + "\r\n" +
                                "================\r\n";
            }
        }

        /// <summary>
        /// 
        /// </summary>
        /// <returns></returns>
        private static bool CreateEventLogSource()
        {
            bool results = true;
            try
            {
                if (!EventLog.SourceExists(_appName))
                {
                    //An event log source should not be created and immediately used.
                    //There is a latency time to enable the source, it should be created
                    //prior to executing the application that uses the source.
                    //Execute this sample a second time to use the new source.
                    EventLog.CreateEventSource(_appName, _appName);
                }
            }
            catch { results = false; }
            return results;
        }

        ////////////////////////////////////////////////////////////////////////// 
        #endregion

        #region ISOReader Support...
        //////////////////////////////////////////////////////////////////////////

        /// <summary>
        /// this is the code that reads the iso
        /// image and retrieves the file we need 
        /// </summary>
        /// <param name="fileWeNeed"></param>
        /// <returns></returns>
        private string LoadISOContentToLocal(string fileWeNeed)
        {
            string loadThis = string.Empty;
            try
            {
                // if output location doesn't end with a slash, add it...
                if (_isoReaderOutputLocation.LastIndexOf('\\') != (_isoReaderOutputLocation.Length - 1)) _isoReaderOutputLocation += '\\';

                // Create our ReaderLocation directory if it doesn't exist
                if (!Directory.Exists(_isoReaderOutputLocation))
                    Directory.CreateDirectory(_isoReaderOutputLocation);


                if (_isoReaderInputFile.Contains(RES.Resources.RES_IndexCSVFileName))
                    // read from CD/DVD
                    loadThis = LoadFromPhysicalStorage(fileWeNeed, loadThis);
                else
                    // read from .ISO file
                    loadThis = LoadFromFileStorage(fileWeNeed, loadThis);
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                UpdateEventViewer(_msgs, EventLogEntryType.Warning);
            }
            finally { }

            return loadThis;
        }

        /// <summary>
        /// Retrieve content from an ISO image file
        /// </summary>
        /// <param name="fileWeNeed"></param>
        /// <param name="loadThis"></param>
        /// <returns></returns>
        private string LoadFromFileStorage(string fileWeNeed, string loadThis)
        {
            try
            {
                //
                // Bug #3681 - Arhive Tool - Restore - 
                //	Unable to read/restore from iso that was copied to physical media
                //
                using (var isoStream = File.OpenRead(_isoReaderInputFile))
                {
                    bool detectJoliet = CDReader.Detect(isoStream);
                    bool detectUDF = UdfReader.Detect(isoStream);

                    #region Read content from ISO files...

                    if (detectJoliet) ProcessJolietCD(fileWeNeed, out loadThis, isoStream);
                    if (detectUDF) ProcessUdfCD(fileWeNeed, out loadThis, isoStream);

                    #endregion

                }
            }
            catch (UnauthorizedAccessException ex)
            {
                // let the user know that they will need
                // to copy the files from the CD/DVD to 
                // their local machine...                
                _msgs = string.Format(RES.Resources.RES_UnableToReadPhysicalMediaAccessDenied, ex.Message);
                PopulateStatusTextBox(_msgs, true);
                MessageBox.Show(RES.Resources.RES_UnableToReadPhysicalMediaAccessDeniedMsg);
            }
            return loadThis;
        }

        /// <summary>
        /// Use the DiscUtils CDReader object
        /// for reading Joliet based ISO files...
        /// </summary>
        /// <param name="fileWeNeed"></param>
        /// <param name="loadThis"></param>
        /// <param name="isoStream"></param>
        /// <returns>Index file name or empty string</returns>
        private void ProcessJolietCD(string fileWeNeed, out string loadThis, FileStream isoStream)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter ProcessJolietCD()...");
            try
            {
                loadThis = string.Empty;
                try
                {
                    // for now only (joliet==true) is acceptable
                    using (var cdReader = new CDReader(isoStream, true))
                    {
                        // find leaf directory... 
                        var leafNode = string.Empty;
                        GetLeafDir(cdReader, string.Empty, ref leafNode);

                        // list all the files embedded in the iso...
                        var files = new List<string>(cdReader.GetFiles(leafNode));

                        // process each file...
                        foreach (var inputFileName in files)
                        {
                            var fixedInputFileName = inputFileName.Split(';')[0];
                            var shortFixedInputFileName =
                                fixedInputFileName.Substring(fixedInputFileName.LastIndexOf('\\') + 1);
                            var outputFileName = _isoReaderOutputLocation +
                                                 shortFixedInputFileName;
                            //
                            // multiple iso files require we make a 
                            // unique version of the "index.csv" name;
                            // so for each iso we will prepend an alpha
                            // value i.e., a_index.csv, b_index.csv, etc...
                            //
                            if (shortFixedInputFileName.Equals(fileWeNeed) ||
                                (shortFixedInputFileName.Contains(RES.Resources.RES_IndexCSVFileName) &&
                                 fileWeNeed.Contains(RES.Resources.RES_IndexCSVFileName)))
                            {
                                lock (_writeIndexContentLock)
                                {
                                    using (Stream inFile = cdReader.OpenFile(fixedInputFileName, FileMode.Open))
                                    {
                                        WriteFileOut(inFile, outputFileName);
                                        loadThis = outputFileName;
                                        inFile.Flush();
                                        //inFile.Close();
                                        break;
                                    }
                                }
                            }
                        }

                        //cdReader.Dispose();
                    }
                }
                catch (Exception ex)
                {
                    _msgs = string.Format(RES.Resources.RES_UnableToOpenFileInViewer);
                    PopulateStatusTextBox(_msgs, true);

                    _msgs = string.Format(RES.Resources.RES_UnableToOpenFileInViewerEventViewer
                                          , ex.Message
                                          , ex.InnerException
                                          , ex.StackTrace);
                    UpdateEventViewer(_msgs);
                    Log.LogWrite(ErrorMessageString(ex));
                }
            }
            finally
            {
                Log.LogWrite("Exit ProcessJolietCD()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// Use the DiscUtils UdfReader object
        /// for reading UDF based ISO files...
        /// </summary>
        /// <param name="fileWeNeed"></param>
        /// <param name="loadThis"></param>
        /// <param name="isoStream"></param>
        /// <returns></returns>
        private void ProcessUdfCD(string fileWeNeed, out string loadThis, FileStream isoStream)
        {
            var stopwatch = new Stopwatch(); stopwatch.Start();
            Log.LogWrite("Enter ProcessUdfCD()...");
            try
            {
                loadThis = string.Empty;
                try
                {
                    using (var udfReader = new UdfReader(isoStream))
                    {
                        // find leaf directory... 
                        string leafNode = string.Empty;
                        GetLeafDir(udfReader, string.Empty, ref leafNode);

                        //// list all the files embedded in the iso...
                        var files = new List<string>(udfReader.GetFiles(leafNode));

                        foreach (var inputFileName in files)
                        {
                            var fixedInputFileName = inputFileName.Split(';')[0];
                            var shortFixedInputFileName =
                                fixedInputFileName.Substring(fixedInputFileName.LastIndexOf('\\') + 1);
                            var outputFileName = _isoReaderOutputLocation +
                                                 shortFixedInputFileName;
                            //
                            // multiple iso files require we make a 
                            // unique version of the "index.csv" name;
                            // so for each iso we will prepend an alpha
                            // value i.e., a_index.csv, b_index.csv, etc...
                            //
                            if (shortFixedInputFileName.Equals(fileWeNeed) ||
                                (shortFixedInputFileName.Contains(RES.Resources.RES_IndexCSVFileName) &&
                                 fileWeNeed.Contains(RES.Resources.RES_IndexCSVFileName)))
                            {
                                lock (_writeIndexContentLock)
                                {
                                    using (Stream inFile = udfReader.OpenFile(fixedInputFileName, FileMode.Open))
                                    {
                                        WriteFileOut(inFile, outputFileName);
                                        loadThis = outputFileName;
                                        inFile.Flush();
                                        //inFile.Close();
                                        break;
                                    }
                                }
                            }
                        }

                        //udfReader.Dispose();
                    }
                }
                catch (Exception ex)
                {
                    _msgs = string.Format(RES.Resources.RES_UnableToOpenFileInViewer);
                    PopulateStatusTextBox(_msgs, true);

                    _msgs = string.Format(RES.Resources.RES_UnableToOpenFileInViewerEventViewer
                                          , ex.Message
                                          , ex.InnerException
                                          , ex.StackTrace);
                    UpdateEventViewer(_msgs);
                    Log.LogWrite(ErrorMessageString(ex));
                }
            }
            finally
            {
                Log.LogWrite("Exit ProcessUdfCD()... " + FormatElapsedTime(stopwatch));
            }
        }

        /// <summary>
        /// Use this to retrieve content that
        /// was burned to CD\DVD
        /// </summary>
        /// <param name="fileWeNeed"></param>
        /// <param name="loadThis"></param>
        /// <returns></returns>
        private static string LoadFromPhysicalStorage(string fileWeNeed, string loadThis)
        {
            //
            // Bug #3680 - Arhive Tool - Restore - 
            //	Unable to read/restore from iso that was burned to physical media
            //

            var directoryInfo = new FileInfo(_isoReaderInputFile).Directory;
            if (directoryInfo != null)
            {
                var fiArray = directoryInfo.GetFiles();
                for (var x = 0; x < fiArray.Length; Interlocked.Increment(ref x))
                {
                    var shortFixedInputFileName = fiArray[x].Name;

                    if (shortFixedInputFileName.Equals(fileWeNeed) ||
                        (shortFixedInputFileName.Contains(RES.Resources.RES_IndexCSVFileName) &&
                         fileWeNeed.Contains(RES.Resources.RES_IndexCSVFileName)))
                    {
                        var inputFileName = new FileInfo(_isoReaderInputFile).DirectoryName + '\\' + fiArray[x].Name;
                        var outputFileName = _isoReaderOutputLocation + shortFixedInputFileName;

                        lock (_writeIndexContentLock)
                        {
                            using (FileStream inFile = File.OpenRead(inputFileName))
                            {
                                WriteFileOut(inFile, outputFileName);
                                loadThis = outputFileName;
                                inFile.Flush();
                                inFile.Close();
                            }
                        }
                        break;
                    }
                }
            }
            return loadThis;
        }

        /// <summary>
        /// simple way to handles reading csv files
        /// without worrying about embedded comma's
        /// </summary>
        /// <param name="path"></param>
        /// <returns></returns>
        public static DataTable ParseCSVComplex(string path)
        {
            if (!File.Exists(path))
                return null;

            return (ParseCSVSimple(path));
        }

        /// <summary>
        /// simple way to handles reading csv files
        /// without worrying about embedded comma's
        /// </summary>
        /// <param name="path"></param>
        /// <returns></returns>
        private static DataTable ParseCSVSimple(string path)
        {
            if (!File.Exists(path))
                return null;

            //create a DataTable to hold the query results
            using (var csvDataTable = new DataTable())
            {
                _msgs = string.Format(RES.Resources.RES_ReadIndexCSVFileSuccessfully, path);

                using (var csv = new CSVReader(path, true))
                {
                    var hdr = csv.ColumnNames;
                    foreach (var s in hdr)
                    {
                        csvDataTable.Columns.Add(s);
                    }
                    try
                    {
                        while (csv.Read())
                        {
                            DataRow row = csvDataTable.NewRow();
                            for (int i = 0; i < csv.FieldCount; i++)
                            {
                                row[i] = csv.GetValue(i);
                            }
                            csvDataTable.Rows.Add(row);
                        }
                    }
                    catch (CSVReadException cre)
                    {
                        if (!cre.Message.ToUpper().Equals("COLUMN COUNT MISMATCH")) throw;
                    }
                    catch (InvalidOperationException e)
                    {
                        // shouldn't be here...
                        _msgs = string.Format(RES.Resources.RES_UnableToReadIndexCSVFileInvalidOperationException, path,
                            e.Message);
                        throw new SRIPArchiveClientFormException(e.Message);
                    }
                    catch (Exception ex)
                    {
                        //
                        // this error occurred when we burned an ISO to a 
                        // CD and the index.csv written was corrupt.
                        // Not sure what we can do about this other than report it...
                        //
                        _msgs = string.Format(RES.Resources.RES_UnableToReadIndexCSVFile, path, ex.Message);
                        throw new SRIPArchiveClientFormException(_msgs);
                    }
                }
                return csvDataTable;
            }
        }

        /// <summary>
        /// find the leaf node on the Joliet ISO
        /// </summary>
        /// <param name="cd"></param>
        /// <param name="fileName"></param>
        /// <param name="leafNode"></param>
        /// <returns></returns>
        private static void GetLeafDir(CDReader cd, string fileName, ref string leafNode)
        {
            try
            {
                foreach (var d in cd.GetDirectories(fileName))
                {
                    GetLeafDir(cd, d, ref leafNode);
                }

                if (cd.GetDirectories(fileName).Length.Equals(0))
                    leafNode = fileName;
            }
            catch { }
        }

        /// <summary>
        /// find the leaf node on the UDF ISO
        /// </summary>
        /// <param name="udfReader"></param>
        /// <param name="fileName"></param>
        /// <param name="leafNode"></param>
        private void GetLeafDir(UdfReader udfReader, string fileName, ref string leafNode)
        {
            foreach (string d in udfReader.GetDirectories(fileName))
            {
                GetLeafDir(udfReader, d, ref leafNode);
            }

            if (udfReader.GetDirectories(fileName).Length.Equals(0))
                leafNode = fileName;
        }

        /// <summary>
        /// push the data we found on the iso
        /// to the given directory
        /// </summary>
        /// <param name="inStream"></param>
        /// <param name="sLocalPath"></param>
        private static void WriteFileOut(Stream inStream, string sLocalPath)
        {
            var chunkSize = 4 * 1024;
            byte[] buffer = new byte[chunkSize];

            using (var reader = new BinaryReader(inStream))
            {
                using (var writer = new BinaryWriter(new FileStream(
                        sLocalPath
                        , FileMode.Create
                        , FileAccess.Write
                        , FileShare.None)))
                {
                    var bytesRead = reader.Read(buffer, 0, chunkSize);
                    FixBufferSizeAsNeeded(ref chunkSize, ref buffer, bytesRead);
                    if (buffer.Length == 0) bytesRead = 0;	// nothing more to send

                    while (bytesRead > 0)
                    {
                        writer.Write(buffer, 0, bytesRead);
                        try
                        {
                            bytesRead = reader.Read(buffer, 0, chunkSize);
                            FixBufferSizeAsNeeded(ref chunkSize, ref buffer, bytesRead);
                            if (buffer.Length == 0) bytesRead = 0;	// nothing more to send

                        }
                        catch { bytesRead = 0; }
                    }
                    writer.Flush();
                    writer.Close();
                }
                reader.Close();
            }
        }

        /// <summary>
        /// insure that the chunk size we applied
        /// is valid - if not, we set the new size - this 
        /// helps us avoid trying to handle a mostly empty buffer        
        /// (could be up to 4K of junk)
        /// </summary>
        /// <param name="chunkSize"></param>
        /// <param name="Buffer"></param>
        /// <param name="bytesRead"></param>
        private static void FixBufferSizeAsNeeded(ref int chunkSize, ref byte[] Buffer, int bytesRead)
        {
            if (bytesRead != Buffer.Length)
            {
                chunkSize = bytesRead;
                byte[] TrimmedBuffer = new byte[bytesRead];
                Array.Copy(Buffer, TrimmedBuffer, bytesRead);
                Buffer = TrimmedBuffer;	// the trimmed buffer should become the new 'buffer'
            }
        }

        //////////////////////////////////////////////////////////////////////////
        #endregion

        #region Deprecated...
        /////////////////////////////////////////////////////////////////////////
        /// <summary>
        /// performs ISO creation work on a background thread
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        [Obsolete("Not in use...", true)]
        private void BgWorkerISOWriterDoWork_Old(object sender, DoWorkEventArgs e)
        {
            Log.LogWrite("1. WAITFOR-PHASE-3 ProcessImageRepositoryObject(): _autoEventIsoWriterCriticalLoop.WaitOne - hold XXXXXXXXXX");
            _autoEventIsoWriterCriticalLoop.WaitOne();
            Log.LogWrite("2. START-PHASE-3a BgWorkerISOWriterDoWork(): _autoEventIsoWriterCriticalLoop.WaitOne - released XXXXXXXXXX");

            var stopwatch = new Stopwatch();
            stopwatch.Start();
            Log.LogWrite("Enter BgWorkerISOWriterDoWork()...");

            _autoEventIsoWriterWorking.Reset();
            _elapsedIsoCreationTime.Reset();
            _elapsedIsoCreationTime.Start();

            _msgs = string.Format("Begin ISO Writer - repository item count: {0}",
                _imageRepository.Items.Count.ToString(CultureInfo.InvariantCulture));
            UpdateEventViewer(_msgs);

            if (_imageRepository.Items.Count < 1)
            {
                e.Result = null;
                return;
            }
            try
            {
                var fileSystemInfos = _imageRepository.Items.ToList();
                fileSystemInfos.ForEach(f => File.Delete(f.FullName));

                e.Result = null;
                var ifsi = _imageRepository as IFileSystemImage;

                _msgs = string.Format("Prepare result image...");
                UpdateEventViewer(_msgs);

                IFileSystemImageResult res = ifsi.CreateResultImage();

                _msgs = string.Format("Is the image null? {0}", (null == res ? "yes" : "no"));
                UpdateEventViewer(_msgs);

                if (res == null)
                    return;

                using (var frm = new ISOFormatter(e.Argument as string))
                {
                    this.Stop += frm.CancelOp;
                    if (_imageRepository.Update != null)
                    {
                        var ev = frm as DiscFormat2Data_Events;
                        ev.Update += AsyncFormattingEvent;
                    }

                    _msgs = string.Format("Prepare to create full image...");
                    UpdateEventViewer(_msgs);

                    frm.CreateFullImage(res);

                    _msgs = string.Format("Full image created...");
                    UpdateEventViewer(_msgs);
                    e.Result = frm;

                    _imageRepository.Reset();
                }

                ifsi = null;
                res = null;
            }
            catch (System.Runtime.InteropServices.COMException ex)
            {
                _cancelledCOMRunTimeError = true;
                if (ex.ErrorCode == -1062555360)
                {
                    _msgs = string.Format("Media size could be too small for the amount of data: Size: {0} bytes",
                        _imageRepository.SizeBeforeFormatting);
                    UpdateEventViewer(_msgs);
                    throw new SRIPArchiveClientFormException(_msgs, ex);
                }
                else
                {
                    if ((uint)ex.ErrorCode == 0x80040154)
                    {
                        _msgs =
                            string.Format(
                                "IMAPI2 is not installed on this machine. See http://support.microsoft.com/kb/KB932716 for details.");

                        if (MessageBox.Show(this, "IMAPI2 is not installed on this machine.\nDo you want to install it?",
                            "Error"
                                , MessageBoxButtons.YesNo
                                , MessageBoxIcon.Exclamation) == DialogResult.Yes)
                        {
                            Process.Start("Iexplore.exe", @"http://support.microsoft.com/kb/KB932716");
                        }


                        UpdateEventViewer(_msgs, EventLogEntryType.Error);
                        throw new SRIPArchiveClientFormException(_msgs, ex);
                    }
                    else
                    {
                        _msgs = string.Format("COM Error: {0} Method: {1}", ex.Message, ex.TargetSite);
                        UpdateEventViewer(_msgs, EventLogEntryType.Error);
                        throw ex;
                    }
                }
            }
            catch (Exception ex)
            {
                _msgs = ErrorMessageString(ex);
                UpdateEventViewer(_msgs, EventLogEntryType.Error);
                e.Result = null;
            }
            finally
            {
                e.Cancel = _bgWorkerISOWriter.CancellationPending;
                Log.LogWrite("Exit BgWorkerISOWriterDoWork()... " + FormatElapsedTime(stopwatch));
                _autoEventIsoWriterWorking.Set();
            }
        }

        /// <summary>
        /// Respond to ISO write completion
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        [Obsolete("Not in use...", true)]
        private void BgWorkerISOWriterRunWorkerCompleted_Old(object sender, RunWorkerCompletedEventArgs e)
        {
            // wait for data to be downloaded...
            Log.LogWrite("1. ENDING-PHASE-3a BgWorkerISOWriterDoWork(): _autoEventIsoWriterWorking.WaitOne - hold XXXXXXXXXX");
            _autoEventIsoWriterWorking.WaitOne();
            Log.LogWrite("2. END-PHASE-3a BgWorkerISOWriterDoWork(): _autoEventIsoWriterWorking.WaitOne - released XXXXXXXXXX");

            var stopwatch = new Stopwatch(); stopwatch.Start();
            try
            {
                Log.LogWrite("Enter _bgWorkerISOWriter_RunWorkerCompleted...");

                if (e.Cancelled || _cancellationISOWriter)
                {
                    _isoImageRepositoryIndex = 0;
                }
                _bgWorkerISOWriter.DoWork -= BgWorkerISOWriterDoWork;
                _bgWorkerISOWriter.RunWorkerCompleted -= BgWorkerISOWriterRunWorkerCompleted;
                _timeRemainingEstimates.Stop();
                WrapUpCompletedEvent(e);

                try
                {
                    if (_isoImageRepositoryIndex > 0)
                    {
                        Interlocked.Decrement(ref _isoImageRepositoryIndex);   // begin clearing
                        Interlocked.Increment(ref _isoIterateImageRepository);
                        _imageRepository = _imageRepositoryList[_isoIterateImageRepository];

                        lock (_createIndexNameLock)
                        {
                            //
                            // fix txtUserName to handle occasions where
                            // the user name is a domain name...
                            //
                            var fixedTxtUserName = txtUserName.Text.Replace("\\", "_");

                            txtOutputLocation.Text =
                                CreateISOImageOutputFileName(new FileInfo(txtOutputLocation.Text)
                                                                 .DirectoryName + "\\" + fixedTxtUserName + "_",
                                    CreateIndexTextValue(_isoIterateImageRepository),
                                    false);
                        }
                        //
                        // Wiederholen Sie diesen!...
                        //
                        _timeRemainingEstimates.Reset(); _timeRemainingEstimates.Start();
                        ProcessImageRepositoryObject();
                    }
                }
                catch (Exception ex)
                {
                    UpdateEventViewer(string.Format("Error in BgWorkerISOWriterRunWorkerCompleted(): {0}", ex.Message));
                }
            }
            finally
            {
                Log.LogWrite("Exit BgWorkerISOWriterRunWorkerCompleted... " + FormatElapsedTime(stopwatch));
            }
        }
        /////////////////////////////////////////////////////////////////////////
        #endregion
    }

    #region Helper Objects...

    static class ArchiveToolExtensions
    {
        /// <summary>
        /// see http://msdn.microsoft.com/en-us/library/aa355056.aspx
        /// for details why we need this extension method
        /// </summary>
        /// <param name="myServiceClient"></param>
        public static void CloseConnection(this ICommunicationObject myServiceClient)
        {
            if (myServiceClient.State != CommunicationState.Opened)
            {
                return;
            }

            try
            {
                Log.LogWrite(@"About to try closing ICommunicationObject object...");
                myServiceClient.Close();
                Log.LogWrite(@"Successfully closed ICommunicationObject object...");
            }
            catch (CommunicationException ex)
            {
                Log.LogWrite(ex.ToString());
                myServiceClient.Abort();
            }
            catch (TimeoutException ex)
            {
                Log.LogWrite(ex.ToString());
                myServiceClient.Abort();
            }
            catch (Exception ex)
            {
                Log.LogWrite(ex.ToString());
                myServiceClient.Abort();
                throw;
            }
        }

        public static TimeSpan Seconds(this int value)
        {
            return new TimeSpan(0, 0, 0, value);
        }

        public static TimeSpan Minutes(this int value)
        {
            return new TimeSpan(0, 0, value, 0);
        }

        public static TimeSpan Hours(this int value)
        {
            return new TimeSpan(0, value, 0, 0);
        }
    }

    /// <summary>
    /// This override is added to *try* and
    /// improve the performance of the webclient.
    /// Microsoft recommends setting the max connection
    /// limit to 12 times the number of CPUs. We will presume
    /// the server is on a 1 CPU machine...
    /// </summary>
    class ArchiveWebClient : WebClient
    {
        public int ArchiveTimeout { get; set; }
        public ArchiveWebClient() { ArchiveTimeout = 120000; } // 2 minutes...
        public ArchiveWebClient(int timeout) { ArchiveTimeout = timeout; }
        protected override WebRequest GetWebRequest(Uri address)
        {
            var request = base.GetWebRequest(address) as HttpWebRequest;
            if (request != null)
            {
                var tempLimit = SRIPArchiveClientForm.NumberOfCPUs * SRIPArchiveClientForm.NumberOfCPUConnections;

                if (!request.ServicePoint.ConnectionLimit.Equals(tempLimit))
                    request.ServicePoint.ConnectionLimit =
                        SRIPArchiveClientForm.NumberOfCPUs * SRIPArchiveClientForm.NumberOfCPUConnections;

                request.KeepAlive = false;
                request.Timeout = request.Timeout.Equals(ArchiveTimeout) ? request.Timeout : ArchiveTimeout;

                SRIPArchiveClientForm.RequestedConnectionLimit = request.ServicePoint.ConnectionLimit;
            }
            return request;
        }
    }

    [Serializable]
    public class ArcDownloadTimeoutException : Exception
    {
        //
        // For guidelines regarding the creation of new exception types, see
        //    http://msdn.microsoft.com/library/default.asp?url=/library/en-us/cpgenref/html/cpconerrorraisinghandlingguidelines.asp
        // and
        //    http://msdn.microsoft.com/library/default.asp?url=/library/en-us/dncscol/html/csharp07192001.asp
        //

        public ArcDownloadTimeoutException()
        {
        }

        public ArcDownloadTimeoutException(string message) : base(message)
        {
        }

        public ArcDownloadTimeoutException(string message, Exception inner) : base(message, inner)
        {
        }

        protected ArcDownloadTimeoutException(SerializationInfo info,StreamingContext context) 
            : base(info, context)
        {
        }
    }

    [Serializable]
    public class SRIPArchiveClientFormException : Exception
    {
        //
        // For guidelines regarding the creation of new exception types, see
        //    http://msdn.microsoft.com/library/default.asp?url=/library/en-us/cpgenref/html/cpconerrorraisinghandlingguidelines.asp
        // and
        //    http://msdn.microsoft.com/library/default.asp?url=/library/en-us/dncscol/html/csharp07192001.asp
        //

        public SRIPArchiveClientFormException() { }
        public SRIPArchiveClientFormException(string message) : base(message) { }
        public SRIPArchiveClientFormException(string message, Exception inner) : base(message, inner) { }
        protected SRIPArchiveClientFormException(SerializationInfo info,StreamingContext context)
            : base(info, context) { }
    }

    #endregion
}
