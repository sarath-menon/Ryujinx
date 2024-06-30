using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Net;
using System.Net.WebSockets;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using System.Timers;
using Avalonia;
using Avalonia.Controls;
using Avalonia.Controls.ApplicationLifetimes;
using Avalonia.Input;
using Avalonia.Threading;
using LibHac.Tools.FsSystem;
using Newtonsoft.Json;
using Ryujinx.Audio.Backends.Dummy;
using Ryujinx.Audio.Backends.OpenAL;
using Ryujinx.Audio.Backends.SDL2;
using Ryujinx.Audio.Backends.SoundIo;
using Ryujinx.Audio.Integration;
using Ryujinx.Ava.Common;
using Ryujinx.Ava.Common.Locale;
using Ryujinx.Ava.Input;
using Ryujinx.Ava.UI.Helpers;
using Ryujinx.Ava.UI.Models;
using Ryujinx.Ava.UI.Renderer;
using Ryujinx.Ava.UI.ViewModels;
using Ryujinx.Ava.UI.Windows;
using Ryujinx.Common;
using Ryujinx.Common.Configuration;
using Ryujinx.Common.Configuration.Multiplayer;
using Ryujinx.Common.Logging;
using Ryujinx.Common.SystemInterop;
using Ryujinx.Common.Utilities;
using Ryujinx.Graphics.GAL;
using Ryujinx.Graphics.GAL.Multithreading;
using Ryujinx.Graphics.Gpu;
using Ryujinx.Graphics.OpenGL;
using Ryujinx.Graphics.Vulkan;
using Ryujinx.HLE;
using Ryujinx.HLE.FileSystem;
using Ryujinx.HLE.HOS;
using Ryujinx.HLE.HOS.Services.Account.Acc;
using Ryujinx.HLE.HOS.SystemState;
using Ryujinx.Input;
using Ryujinx.Input.HLE;
using Ryujinx.UI.App.Common;
using Ryujinx.UI.Common;
using Ryujinx.UI.Common.Configuration;
using Ryujinx.UI.Common.Helper;
using SharpHook;
using SharpHook.Native;
using Silk.NET.Vulkan;
using SixLabors.ImageSharp;
using SixLabors.ImageSharp.Formats.Jpeg;
using SixLabors.ImageSharp.Formats.Png;
using SixLabors.ImageSharp.PixelFormats;
using SixLabors.ImageSharp.Processing;
using SPB.Graphics.Vulkan;
using static Ryujinx.Ava.UI.Helpers.Win32NativeInterop;
using AntiAliasing = Ryujinx.Common.Configuration.AntiAliasing;
using Image = SixLabors.ImageSharp.Image;
using InputManager = Ryujinx.Input.HLE.InputManager;
using IRenderer = Ryujinx.Graphics.GAL.IRenderer;
using Key = Ryujinx.Input.Key;
using MouseButton = Ryujinx.Input.MouseButton;
using ScalingFilter = Ryujinx.Common.Configuration.ScalingFilter;
using Size = Avalonia.Size;
using Switch = Ryujinx.HLE.Switch;

namespace Ryujinx.Ava
{
    internal class AppHost
    {
        // for http server
        private HttpListener _httpListener;

        // Add a list to track all open WebSockets
        private List<WebSocket> _openWebSockets = new List<WebSocket>();

        // for simulating mouse events
        private EventSimulator _eventSimulator = new EventSimulator();

        // private System.Timers.Timer _messageTimer;
        private byte[] _imageByte;
        private Image _image;

        private const int CursorHideIdleTime = 5; // Hide Cursor seconds.
        private const float MaxResolutionScale = 4.0f; // Max resolution hotkeys can scale to before wrapping.
        private const int TargetFps = 60;
        private const float VolumeDelta = 0.05f;

        private static readonly Cursor _invisibleCursor = new(StandardCursorType.None);
        private readonly IntPtr _invisibleCursorWin;
        private readonly IntPtr _defaultCursorWin;

        private readonly long _ticksPerFrame;
        private readonly Stopwatch _chrono;
        private long _ticks;

        private readonly AccountManager _accountManager;
        private readonly UserChannelPersistence _userChannelPersistence;
        private readonly InputManager _inputManager;

        private readonly MainWindowViewModel _viewModel;
        private readonly IKeyboard _keyboardInterface;
        private readonly IMouse _mouseInterface;
        private readonly TopLevel _topLevel;
        public RendererHost RendererHost;

        private readonly GraphicsDebugLevel _glLogLevel;
        private float _newVolume;
        private KeyboardHotkeyState _prevHotkeyState;

        private long _lastCursorMoveTime;
        private bool _isCursorInRenderer = true;
        private bool _ignoreCursorState = false;

        private enum CursorStates
        {
            CursorIsHidden,
            CursorIsVisible,
            ForceChangeCursor
        };

        private CursorStates _cursorState = !ConfigurationState.Instance.Hid.EnableMouse.Value
            ? CursorStates.CursorIsVisible
            : CursorStates.CursorIsHidden;

        private bool _isStopped;
        private bool _isActive;
        private bool _renderingStarted;

        private readonly ManualResetEvent _gpuDoneEvent;

        private IRenderer _renderer;
        private readonly Thread _renderingThread;
        private readonly CancellationTokenSource _gpuCancellationTokenSource;
        private WindowsMultimediaTimerResolution _windowsMultimediaTimerResolution;

        private bool _dialogShown;
        private readonly bool _isFirmwareTitle;

        private readonly object _lockObject = new();
        private readonly object _imageLock = new();

        public event EventHandler AppExit;
        public event EventHandler<StatusInitEventArgs> StatusInitEvent;
        public event EventHandler<StatusUpdatedEventArgs> StatusUpdatedEvent;

        public VirtualFileSystem VirtualFileSystem { get; }
        public ContentManager ContentManager { get; }
        public NpadManager NpadManager { get; }
        public TouchScreenManager TouchScreenManager { get; }
        public Switch Device { get; set; }

        public int Width { get; private set; }
        public int Height { get; private set; }
        public string ApplicationPath { get; private set; }
        public bool ScreenshotRequested { get; set; }

        public AppHost(
            RendererHost renderer,
            InputManager inputManager,
            string applicationPath,
            VirtualFileSystem virtualFileSystem,
            ContentManager contentManager,
            AccountManager accountManager,
            UserChannelPersistence userChannelPersistence,
            MainWindowViewModel viewmodel,
            TopLevel topLevel
        )
        {
            _viewModel = viewmodel;
            _inputManager = inputManager;
            _accountManager = accountManager;
            _userChannelPersistence = userChannelPersistence;
            _renderingThread = new Thread(RenderLoop) { Name = "GUI.RenderThread" };
            _lastCursorMoveTime = Stopwatch.GetTimestamp();
            _glLogLevel = ConfigurationState.Instance.Logger.GraphicsDebugLevel;
            _topLevel = topLevel;

            _inputManager.SetMouseDriver(new AvaloniaMouseDriver(_topLevel, renderer));

            _keyboardInterface = (IKeyboard)_inputManager.KeyboardDriver.GetGamepad("0");
            _mouseInterface = (IMouse)_inputManager.MouseDriver.GetGamepad("0");

            NpadManager = _inputManager.CreateNpadManager();
            TouchScreenManager = _inputManager.CreateTouchScreenManager();
            ApplicationPath = applicationPath;
            VirtualFileSystem = virtualFileSystem;
            ContentManager = contentManager;

            RendererHost = renderer;

            _chrono = new Stopwatch();
            _ticksPerFrame = Stopwatch.Frequency / TargetFps;

            if (ApplicationPath.StartsWith("@SystemContent"))
            {
                ApplicationPath = VirtualFileSystem.SwitchPathToSystemPath(ApplicationPath);

                _isFirmwareTitle = true;
            }

            ConfigurationState.Instance.HideCursor.Event += HideCursorState_Changed;

            _topLevel.PointerMoved += TopLevel_PointerEnteredOrMoved;
            _topLevel.PointerEntered += TopLevel_PointerEnteredOrMoved;
            _topLevel.PointerExited += TopLevel_PointerExited;

            if (OperatingSystem.IsWindows())
            {
                _invisibleCursorWin = CreateEmptyCursor();
                _defaultCursorWin = CreateArrowCursor();
            }

            ConfigurationState.Instance.System.IgnoreMissingServices.Event +=
                UpdateIgnoreMissingServicesState;
            ConfigurationState.Instance.Graphics.AspectRatio.Event += UpdateAspectRatioState;
            ConfigurationState.Instance.System.EnableDockedMode.Event += UpdateDockedModeState;
            ConfigurationState.Instance.System.AudioVolume.Event += UpdateAudioVolumeState;
            ConfigurationState.Instance.System.EnableDockedMode.Event += UpdateDockedModeState;
            ConfigurationState.Instance.System.AudioVolume.Event += UpdateAudioVolumeState;
            ConfigurationState.Instance.Graphics.AntiAliasing.Event += UpdateAntiAliasing;
            ConfigurationState.Instance.Graphics.ScalingFilter.Event += UpdateScalingFilter;
            ConfigurationState.Instance.Graphics.ScalingFilterLevel.Event +=
                UpdateScalingFilterLevel;
            ConfigurationState.Instance.Graphics.EnableColorSpacePassthrough.Event +=
                UpdateColorSpacePassthrough;

            ConfigurationState.Instance.System.EnableInternetAccess.Event +=
                UpdateEnableInternetAccessState;
            ConfigurationState.Instance.Multiplayer.LanInterfaceId.Event +=
                UpdateLanInterfaceIdState;
            ConfigurationState.Instance.Multiplayer.Mode.Event += UpdateMultiplayerModeState;

            _gpuCancellationTokenSource = new CancellationTokenSource();
            _gpuDoneEvent = new ManualResetEvent(false);
        }

        private async Task HandleWebSocketConnection(HttpListenerContext context)
        {
            if (!context.Request.IsWebSocketRequest)
            {
                context.Response.StatusCode = 400;
                context.Response.Close();
                return;
            }

            WebSocket webSocket = null;
            try
            {
                var webSocketContext = await context.AcceptWebSocketAsync(subProtocol: null);
                webSocket = webSocketContext.WebSocket;
                _openWebSockets.Add(webSocket); // Track the WebSocket

                var buffer = new ArraySegment<byte>(new byte[2048]);
                while (webSocket != null && webSocket.State == WebSocketState.Open)
                {
                    WebSocketReceiveResult result = await webSocket.ReceiveAsync(
                        buffer,
                        CancellationToken.None
                    );

                    if (!result.EndOfMessage || buffer.Array == null)
                        continue;

                    // deserialize the message
                    string message = Encoding.UTF8.GetString(
                        buffer.Array,
                        buffer.Offset,
                        result.Count
                    );
                    var requestData = JsonConvert.DeserializeObject<Dictionary<string, string>>(
                        message
                    );
                    if (requestData == null)
                        continue;

                    await ProcessWebSocketRequest(context, webSocket, requestData);
                }
            }
            catch (Exception e)
            {
                Console.WriteLine($"WebSocket error: {e.Message}");
            }
            finally
            {
                if (webSocket != null && webSocket.State != WebSocketState.Closed)
                {
                    await webSocket.CloseAsync(
                        WebSocketCloseStatus.InternalServerError,
                        "Error occurred",
                        CancellationToken.None
                    );
                }
                _openWebSockets.Remove(webSocket); // Remove from tracking list
            }
        }

        private async Task ProcessWebSocketRequest(
            HttpListenerContext context,
            WebSocket webSocket,
            Dictionary<string, string> requestData
        )
        {
            string endpointName = context.Request.RawUrl;
            switch (endpointName)
            {
                case "/stream_websocket":
                    if (
                        requestData.TryGetValue("action", out string action)
                        && action == "request_frames"
                    )
                    {
                        int frameCount = int.TryParse(requestData["count"], out int count)
                            ? count
                            : 1;
                        await SendFrameAsWebSocket(webSocket, frameCount);
                    }
                    break;
                case "/keypress_websocket":
                    if (
                        requestData.TryGetValue("key", out string key)
                        && requestData.TryGetValue("duration", out string durationStr)
                    )
                    {
                        Enum.TryParse<Key>(key, out Key avaKey);
                        int.TryParse(durationStr, out int duration);
                        await DoKeypress(webSocket, avaKey, duration);
                    }
                    break;
                default:
                    await SendErrorMessage(webSocket, "Unsupported endpoint");
                    break;
            }
        }

        public void CloseAllWebSockets()
        {
            foreach (var webSocket in _openWebSockets)
            {
                if (webSocket.State != WebSocketState.Open)
                    continue;

                webSocket
                    .CloseAsync(
                        WebSocketCloseStatus.NormalClosure,
                        "Closing",
                        CancellationToken.None
                    )
                    .Wait();
            }
            _openWebSockets.Clear();
        }

        private async Task DoKeypress(WebSocket webSocket, Key avaKey, int duration)
        {
            (_keyboardInterface as AvaloniaKeyboard)?.EmulateKeyPress(avaKey);
            await Task.Delay(duration);
            (_keyboardInterface as AvaloniaKeyboard)?.EmulateKeyRelease(avaKey);

            // Send response back to client
            string responseMessage = "Status: OK";
            byte[] responseBuffer = Encoding.UTF8.GetBytes(responseMessage);
            await webSocket.SendAsync(
                new ArraySegment<byte>(responseBuffer),
                WebSocketMessageType.Text,
                true,
                CancellationToken.None
            );
        }

        private async Task SendErrorMessage(WebSocket webSocket, string errorMessage)
        {
            byte[] errorBuffer = Encoding.UTF8.GetBytes(errorMessage);
            await webSocket.SendAsync(
                new ArraySegment<byte>(errorBuffer),
                WebSocketMessageType.Text,
                true,
                CancellationToken.None
            );
        }

        private async Task SendFrameAsWebSocket(WebSocket webSocket, int frameCount)
        {
            for (int i = 0; i < frameCount; i++)
            {
                byte[] frameData;
                lock (_imageLock)
                {
                    if (_imageByte != null)
                    {
                        frameData = _imageByte;
                    }
                    else
                    {
                        frameData = Encoding.UTF8.GetBytes("No frame available");
                    }
                }

                await webSocket.SendAsync(
                    new ArraySegment<byte>(frameData),
                    WebSocketMessageType.Binary,
                    endOfMessage: true,
                    CancellationToken.None
                );

                if (i < frameCount - 1) // Wait for a short interval before sending the next frame
                {
                    await Task.Delay(1);
                }
            }
        }

        private async Task HandlePostRequest(HttpListenerRequest request)
        {
            try
            {
                switch (request.Url.AbsolutePath)
                {
                    case "/resume_game":
                        Console.WriteLine("Resume game");
                        await Task.Run(() => Resume()); // Ensure method is properly awaited if it's async
                        break;
                    case "/pause_game":
                        Console.WriteLine("Pause game");
                        await Task.Run(() => Pause()); // Ensure method is properly awaited if it's async
                        break;
                    case "/mouse_press":
                        Console.WriteLine("Mouse press");
                        // Move the mouse pointer to (0, 0)
                        _eventSimulator.SimulateMouseMovement(500, 500);
                        break;
                }
            }
            catch (Exception ex)
            {
                Console.WriteLine("Error handling game action: " + ex.Message);
            }
        }

        // Update the method where the Timer is instantiated
        private void StartHttpServer()
        {
            _httpListener = new HttpListener();
            _httpListener.Prefixes.Add("http://localhost:8086/");
            _httpListener.Start();

            _httpListener.BeginGetContext(new AsyncCallback(ListenerCallback), _httpListener);
        }

        // Add this callback method to handle incoming HTTP requests
        // Update the method where WebSocket connections are handled
        private async void ListenerCallback(IAsyncResult result)
        {
            HttpListener listener = (HttpListener)result.AsyncState;
            HttpListenerContext context = null;

            try
            {
                context = await Task.Run(() => listener.EndGetContext(result));
            }
            catch (Exception ex) // Now using the exception variable
            {
                Console.WriteLine("Listener exception: " + ex.Message);
                return;
            }

            // Handle each request in a new task
            Task.Run(async () =>
            {
                HttpListenerRequest request = context.Request;
                HttpListenerResponse response = context.Response;

                try
                {
                    if (request.IsWebSocketRequest)
                    {
                        await HandleWebSocketConnection(context);
                    }
                    else if (request.HttpMethod == "POST")
                    {
                        await HandlePostRequest(request);
                    }
                    else
                    {
                        response.StatusCode = 404; // Not Found
                        response.StatusDescription = "Not Found";
                    }
                }
                catch (Exception ex) // Now using the exception variable
                {
                    Console.WriteLine("Error processing request: " + ex.Message);
                }
                finally
                {
                    response.Close();
                }
            });

            listener.BeginGetContext(new AsyncCallback(ListenerCallback), listener);
        }

        private void TopLevel_PointerEnteredOrMoved(object sender, PointerEventArgs e)
        {
            if (!_viewModel.IsActive)
            {
                _isCursorInRenderer = false;
                _ignoreCursorState = false;
                return;
            }

            if (sender is MainWindow window)
            {
                if (ConfigurationState.Instance.HideCursor.Value == HideCursorMode.OnIdle)
                {
                    _lastCursorMoveTime = Stopwatch.GetTimestamp();
                }

                var point = e.GetCurrentPoint(window).Position;
                var bounds = RendererHost.EmbeddedWindow.Bounds;
                var windowYOffset = bounds.Y + window.MenuBarHeight;
                var windowYLimit = (int)window.Bounds.Height - window.StatusBarHeight - 1;

                if (!_viewModel.ShowMenuAndStatusBar)
                {
                    windowYOffset -= window.MenuBarHeight;
                    windowYLimit += window.StatusBarHeight + 1;
                }

                _isCursorInRenderer =
                    point.X >= bounds.X
                    && Math.Ceiling(point.X) <= (int)window.Bounds.Width
                    && point.Y >= windowYOffset
                    && point.Y <= windowYLimit
                    && !_viewModel.IsSubMenuOpen;

                _ignoreCursorState = false;
            }
        }

        private void TopLevel_PointerExited(object sender, PointerEventArgs e)
        {
            _isCursorInRenderer = false;

            if (sender is MainWindow window)
            {
                var point = e.GetCurrentPoint(window).Position;
                var bounds = RendererHost.EmbeddedWindow.Bounds;
                var windowYOffset = bounds.Y + window.MenuBarHeight;
                var windowYLimit = (int)window.Bounds.Height - window.StatusBarHeight - 1;

                if (!_viewModel.ShowMenuAndStatusBar)
                {
                    windowYOffset -= window.MenuBarHeight;
                    windowYLimit += window.StatusBarHeight + 1;
                }

                _ignoreCursorState =
                    (point.X == bounds.X || Math.Ceiling(point.X) == (int)window.Bounds.Width)
                    && point.Y >= windowYOffset
                    && point.Y <= windowYLimit;
            }

            _cursorState = CursorStates.ForceChangeCursor;
        }

        private void UpdateScalingFilterLevel(object sender, ReactiveEventArgs<int> e)
        {
            _renderer.Window?.SetScalingFilter(
                (Graphics.GAL.ScalingFilter)ConfigurationState.Instance.Graphics.ScalingFilter.Value
            );
            _renderer.Window?.SetScalingFilterLevel(
                ConfigurationState.Instance.Graphics.ScalingFilterLevel.Value
            );
        }

        private void UpdateScalingFilter(object sender, ReactiveEventArgs<ScalingFilter> e)
        {
            _renderer.Window?.SetScalingFilter(
                (Graphics.GAL.ScalingFilter)ConfigurationState.Instance.Graphics.ScalingFilter.Value
            );
            _renderer.Window?.SetScalingFilterLevel(
                ConfigurationState.Instance.Graphics.ScalingFilterLevel.Value
            );
        }

        private void UpdateColorSpacePassthrough(object sender, ReactiveEventArgs<bool> e)
        {
            _renderer.Window?.SetColorSpacePassthrough(
                (bool)ConfigurationState.Instance.Graphics.EnableColorSpacePassthrough.Value
            );
        }

        private void ShowCursor()
        {
            Dispatcher.UIThread.Post(() =>
            {
                _viewModel.Cursor = Cursor.Default;

                if (OperatingSystem.IsWindows())
                {
                    if (_cursorState != CursorStates.CursorIsHidden && !_ignoreCursorState)
                    {
                        SetCursor(_defaultCursorWin);
                    }
                }
            });

            _cursorState = CursorStates.CursorIsVisible;
        }

        private void HideCursor()
        {
            Dispatcher.UIThread.Post(() =>
            {
                _viewModel.Cursor = _invisibleCursor;

                if (OperatingSystem.IsWindows())
                {
                    SetCursor(_invisibleCursorWin);
                }
            });

            _cursorState = CursorStates.CursorIsHidden;
        }

        private void SetRendererWindowSize(Size size)
        {
            if (_renderer != null)
            {
                double scale = _topLevel.RenderScaling;

                _renderer.Window?.SetSize((int)(size.Width * scale), (int)(size.Height * scale));
            }
        }

        private void Renderer_ScreenCaptured(object sender, ScreenCaptureImageInfo e)
        {
            // Check if the captured screen data is valid
            if (e.Data.Length > 0 && e.Height > 0 && e.Width > 0)
            {
                // Run the screen capture processing in a separate task
                Task.Run(() =>
                {
                    lock (_lockObject)
                    {
                        // Get the active application name and sanitize it for file naming
                        string applicationName = Device.Processes.ActiveApplication.Name;
                        string sanitizedApplicationName = FileSystemUtils.SanitizeFileName(
                            applicationName
                        );
                        DateTime currentTime = DateTime.Now;

                        // Create a filename for the screenshot
                        string filename =
                            $"{sanitizedApplicationName}_{currentTime.Year}-{currentTime.Month:D2}-{currentTime.Day:D2}_{currentTime.Hour:D2}-{currentTime.Minute:D2}-{currentTime.Second:D2}.png";

                        // Determine the directory to save the screenshot based on the launch mode
                        string directory = AppDataManager.Mode switch
                        {
                            AppDataManager.LaunchMode.Portable
                            or AppDataManager.LaunchMode.Custom
                                => Path.Combine(AppDataManager.BaseDirPath, "screenshots"),
                            _
                                => Path.Combine(
                                    Environment.GetFolderPath(Environment.SpecialFolder.MyPictures),
                                    "Ryujinx"
                                ),
                        };

                        string path = Path.Combine(directory, filename);

                        try
                        {
                            // Create the directory if it doesn't exist
                            Directory.CreateDirectory(directory);
                        }
                        catch (Exception ex)
                        {
                            // Log an error if the directory creation fails
                            Logger.Error?.Print(
                                LogClass.Application,
                                $"Failed to create directory at path {directory}. Error : {ex.GetType().Name}",
                                "Screenshot"
                            );

                            return;
                        }

                        lock (_imageLock)
                        {
                            // Load the image data
                            _image = e.IsBgra
                                ? Image.LoadPixelData<Bgra32>(e.Data, e.Width, e.Height)
                                : Image.LoadPixelData<Rgba32>(e.Data, e.Width, e.Height);

                            // Apply horizontal flip if needed
                            if (e.FlipX)
                            {
                                _image.Mutate(x => x.Flip(FlipMode.Horizontal));
                            }

                            // Apply vertical flip if needed
                            if (e.FlipY)
                            {
                                _image.Mutate(x => x.Flip(FlipMode.Vertical));
                            }

                            // Save the image as a PNG file
                            _image.SaveAsPng(
                                path,
                                new PngEncoder { ColorType = PngColorType.Rgb, }
                            );

                            // // Dispose of the image to free resources
                            // _image.Dispose();

                            // Log a notice that the screenshot was saved successfully
                            Logger.Notice.Print(
                                LogClass.Application,
                                $"Screenshot saved to {path}",
                                "Screenshot"
                            );
                        }
                    }
                });
            }
            else
            {
                // Log an error if the screenshot data is empty or invalid
                Logger.Error?.Print(
                    LogClass.Application,
                    $"Screenshot is empty. Size : {e.Data.Length} bytes. Resolution : {e.Width}x{e.Height}",
                    "Screenshot"
                );
            }
        }

        private void Renderer_ScreenCapturedNoSave(object sender, ScreenCaptureImageInfo e)
        {
            // Check if the captured screen data is valid
            if (e.Data.Length > 0 && e.Height > 0 && e.Width > 0)
            {
                // Run the screen capture processing in a separate task
                Task.Run(() =>
                {
                    lock (_imageLock)
                    {
                        _image = e.IsBgra
                            ? Image.LoadPixelData<Bgra32>(e.Data, e.Width, e.Height)
                            : Image.LoadPixelData<Rgba32>(e.Data, e.Width, e.Height);

                        _imageByte = e.Data;

                        // Apply horizontal flip if needed
                        if (e.FlipX)
                        {
                            _image.Mutate(x => x.Flip(FlipMode.Horizontal));
                        }

                        // Apply vertical flip if needed
                        if (e.FlipY)
                        {
                            _image.Mutate(x => x.Flip(FlipMode.Vertical));
                        }

                        // // Dispose of the image to free resources
                        // _image.Dispose();

                        // // Log a notice that the screenshot was saved successfully
                        // Logger.Notice.Print(
                        //     LogClass.Application,
                        //     $"Screenshot saved to {path}",
                        //     "Screenshot"
                        // );
                    }
                    // }
                });
            }
            else
            {
                // Log an error if the screenshot data is empty or invalid
                Logger.Error?.Print(
                    LogClass.Application,
                    $"Screenshot is empty. Size : {e.Data.Length} bytes. Resolution : {e.Width}x{e.Height}",
                    "Screenshot"
                );
            }
        }

        public void Start()
        {
            if (OperatingSystem.IsWindows())
            {
                _windowsMultimediaTimerResolution = new WindowsMultimediaTimerResolution(1);
            }

            DisplaySleep.Prevent();

            NpadManager.Initialize(
                Device,
                ConfigurationState.Instance.Hid.InputConfig,
                ConfigurationState.Instance.Hid.EnableKeyboard,
                ConfigurationState.Instance.Hid.EnableMouse
            );
            TouchScreenManager.Initialize(Device);

            _viewModel.IsGameRunning = true;

            Dispatcher.UIThread.InvokeAsync(() =>
            {
                _viewModel.Title = TitleHelper.ActiveApplicationTitle(
                    Device.Processes.ActiveApplication,
                    Program.Version
                );
            });

            _viewModel.SetUiProgressHandlers(Device);

            RendererHost.BoundsChanged += Window_BoundsChanged;

            _isActive = true;

            _renderingThread.Start();

            _viewModel.Volume = ConfigurationState.Instance.System.AudioVolume.Value;

            StartHttpServer();

            MainLoop();

            Exit();
        }

        private void UpdateIgnoreMissingServicesState(object sender, ReactiveEventArgs<bool> args)
        {
            if (Device != null)
            {
                Device.Configuration.IgnoreMissingServices = args.NewValue;
            }
        }

        private void UpdateAspectRatioState(object sender, ReactiveEventArgs<AspectRatio> args)
        {
            if (Device != null)
            {
                Device.Configuration.AspectRatio = args.NewValue;
            }
        }

        private void UpdateAntiAliasing(object sender, ReactiveEventArgs<AntiAliasing> e)
        {
            _renderer?.Window?.SetAntiAliasing((Graphics.GAL.AntiAliasing)e.NewValue);
        }

        private void UpdateDockedModeState(object sender, ReactiveEventArgs<bool> e)
        {
            Device?.System.ChangeDockedModeState(e.NewValue);
        }

        private void UpdateAudioVolumeState(object sender, ReactiveEventArgs<float> e)
        {
            Device?.SetVolume(e.NewValue);

            Dispatcher.UIThread.Post(() =>
            {
                _viewModel.Volume = e.NewValue;
            });
        }

        private void UpdateEnableInternetAccessState(object sender, ReactiveEventArgs<bool> e)
        {
            Device.Configuration.EnableInternetAccess = e.NewValue;
        }

        private void UpdateLanInterfaceIdState(object sender, ReactiveEventArgs<string> e)
        {
            Device.Configuration.MultiplayerLanInterfaceId = e.NewValue;
        }

        private void UpdateMultiplayerModeState(object sender, ReactiveEventArgs<MultiplayerMode> e)
        {
            Device.Configuration.MultiplayerMode = e.NewValue;
        }

        public void ToggleVSync()
        {
            Device.EnableDeviceVsync = !Device.EnableDeviceVsync;
            _renderer.Window.ChangeVSyncMode(Device.EnableDeviceVsync);
        }

        public void Stop()
        {
            _isActive = false;
        }

        private void Exit()
        {
            (_keyboardInterface as AvaloniaKeyboard)?.Clear();

            if (_isStopped)
            {
                return;
            }

            _isStopped = true;
            _isActive = false;
        }

        public void DisposeContext()
        {
            Dispose();

            _isActive = false;

            // NOTE: The render loop is allowed to stay alive until the renderer itself is disposed, as it may handle resource dispose.
            // We only need to wait for all commands submitted during the main gpu loop to be processed.
            _gpuDoneEvent.WaitOne();
            _gpuDoneEvent.Dispose();

            DisplaySleep.Restore();

            NpadManager.Dispose();
            TouchScreenManager.Dispose();
            Device.Dispose();

            DisposeGpu();

            AppExit?.Invoke(this, EventArgs.Empty);
        }

        private void Dispose()
        {
            if (Device.Processes != null)
            {
                MainWindowViewModel.UpdateGameMetadata(
                    Device.Processes.ActiveApplication.ProgramIdText
                );
            }

            ConfigurationState.Instance.System.IgnoreMissingServices.Event -=
                UpdateIgnoreMissingServicesState;
            ConfigurationState.Instance.Graphics.AspectRatio.Event -= UpdateAspectRatioState;
            ConfigurationState.Instance.System.EnableDockedMode.Event -= UpdateDockedModeState;
            ConfigurationState.Instance.System.AudioVolume.Event -= UpdateAudioVolumeState;
            ConfigurationState.Instance.Graphics.ScalingFilter.Event -= UpdateScalingFilter;
            ConfigurationState.Instance.Graphics.ScalingFilterLevel.Event -=
                UpdateScalingFilterLevel;
            ConfigurationState.Instance.Graphics.AntiAliasing.Event -= UpdateAntiAliasing;
            ConfigurationState.Instance.Graphics.EnableColorSpacePassthrough.Event -=
                UpdateColorSpacePassthrough;

            _topLevel.PointerMoved -= TopLevel_PointerEnteredOrMoved;
            _topLevel.PointerEntered -= TopLevel_PointerEnteredOrMoved;
            _topLevel.PointerExited -= TopLevel_PointerExited;

            _gpuCancellationTokenSource.Cancel();
            _gpuCancellationTokenSource.Dispose();

            _chrono.Stop();

            if (_httpListener != null)
            {
                _httpListener.Stop();
                _httpListener.Close();
            }

            CloseAllWebSockets();
        }

        public void DisposeGpu()
        {
            if (OperatingSystem.IsWindows())
            {
                _windowsMultimediaTimerResolution?.Dispose();
                _windowsMultimediaTimerResolution = null;
            }

            if (RendererHost.EmbeddedWindow is EmbeddedWindowOpenGL openGlWindow)
            {
                // Try to bind the OpenGL context before calling the shutdown event.
                openGlWindow.MakeCurrent(false, false);

                Device.DisposeGpu();

                // Unbind context and destroy everything.
                openGlWindow.MakeCurrent(true, false);
            }
            else
            {
                Device.DisposeGpu();
            }
        }

        private void HideCursorState_Changed(object sender, ReactiveEventArgs<HideCursorMode> state)
        {
            if (state.NewValue == HideCursorMode.OnIdle)
            {
                _lastCursorMoveTime = Stopwatch.GetTimestamp();
            }

            _cursorState = CursorStates.ForceChangeCursor;
        }

        public async Task<bool> LoadGuestApplication()
        {
            InitializeSwitchInstance();
            MainWindow.UpdateGraphicsConfig();

            SystemVersion firmwareVersion = ContentManager.GetCurrentFirmwareVersion();

            if (
                Application.Current.ApplicationLifetime
                is IClassicDesktopStyleApplicationLifetime desktop
            )
            {
                if (
                    !SetupValidator.CanStartApplication(
                        ContentManager,
                        ApplicationPath,
                        out UserError userError
                    )
                )
                {
                    {
                        if (
                            SetupValidator.CanFixStartApplication(
                                ContentManager,
                                ApplicationPath,
                                userError,
                                out firmwareVersion
                            )
                        )
                        {
                            if (userError == UserError.NoFirmware)
                            {
                                UserResult result =
                                    await ContentDialogHelper.CreateConfirmationDialog(
                                        LocaleManager.Instance[
                                            LocaleKeys.DialogFirmwareNoFirmwareInstalledMessage
                                        ],
                                        LocaleManager.Instance.UpdateAndGetDynamicValue(
                                            LocaleKeys.DialogFirmwareInstallEmbeddedMessage,
                                            firmwareVersion.VersionString
                                        ),
                                        LocaleManager.Instance[LocaleKeys.InputDialogYes],
                                        LocaleManager.Instance[LocaleKeys.InputDialogNo],
                                        ""
                                    );

                                if (result != UserResult.Yes)
                                {
                                    await UserErrorDialog.ShowUserErrorDialog(userError);
                                    Device.Dispose();

                                    return false;
                                }
                            }

                            if (
                                !SetupValidator.TryFixStartApplication(
                                    ContentManager,
                                    ApplicationPath,
                                    userError,
                                    out _
                                )
                            )
                            {
                                await UserErrorDialog.ShowUserErrorDialog(userError);
                                Device.Dispose();

                                return false;
                            }

                            // Tell the user that we installed a firmware for them.
                            if (userError == UserError.NoFirmware)
                            {
                                firmwareVersion = ContentManager.GetCurrentFirmwareVersion();

                                _viewModel.RefreshFirmwareStatus();

                                await ContentDialogHelper.CreateInfoDialog(
                                    LocaleManager.Instance.UpdateAndGetDynamicValue(
                                        LocaleKeys.DialogFirmwareInstalledMessage,
                                        firmwareVersion.VersionString
                                    ),
                                    LocaleManager.Instance.UpdateAndGetDynamicValue(
                                        LocaleKeys.DialogFirmwareInstallEmbeddedSuccessMessage,
                                        firmwareVersion.VersionString
                                    ),
                                    LocaleManager.Instance[LocaleKeys.InputDialogOk],
                                    "",
                                    LocaleManager.Instance[LocaleKeys.RyujinxInfo]
                                );
                            }
                        }
                        else
                        {
                            await UserErrorDialog.ShowUserErrorDialog(userError);
                            Device.Dispose();

                            return false;
                        }
                    }
                }
            }

            Logger.Notice.Print(
                LogClass.Application,
                $"Using Firmware Version: {firmwareVersion?.VersionString}"
            );

            if (_isFirmwareTitle)
            {
                Logger.Info?.Print(LogClass.Application, "Loading as Firmware Title (NCA).");

                if (!Device.LoadNca(ApplicationPath))
                {
                    Device.Dispose();

                    return false;
                }
            }
            else if (Directory.Exists(ApplicationPath))
            {
                string[] romFsFiles = Directory.GetFiles(ApplicationPath, "*.istorage");

                if (romFsFiles.Length == 0)
                {
                    romFsFiles = Directory.GetFiles(ApplicationPath, "*.romfs");
                }

                if (romFsFiles.Length > 0)
                {
                    Logger.Info?.Print(LogClass.Application, "Loading as cart with RomFS.");

                    if (!Device.LoadCart(ApplicationPath, romFsFiles[0]))
                    {
                        Device.Dispose();

                        return false;
                    }
                }
                else
                {
                    Logger.Info?.Print(LogClass.Application, "Loading as cart WITHOUT RomFS.");

                    if (!Device.LoadCart(ApplicationPath))
                    {
                        Device.Dispose();

                        return false;
                    }
                }
            }
            else if (File.Exists(ApplicationPath))
            {
                switch (Path.GetExtension(ApplicationPath).ToLowerInvariant())
                {
                    case ".xci":
                    {
                        Logger.Info?.Print(LogClass.Application, "Loading as XCI.");

                        if (!Device.LoadXci(ApplicationPath))
                        {
                            Device.Dispose();

                            return false;
                        }

                        break;
                    }
                    case ".nca":
                    {
                        Logger.Info?.Print(LogClass.Application, "Loading as NCA.");

                        if (!Device.LoadNca(ApplicationPath))
                        {
                            Device.Dispose();

                            return false;
                        }

                        break;
                    }
                    case ".nsp":
                    case ".pfs0":
                    {
                        Logger.Info?.Print(LogClass.Application, "Loading as NSP.");

                        if (!Device.LoadNsp(ApplicationPath))
                        {
                            Device.Dispose();

                            return false;
                        }

                        break;
                    }
                    default:
                    {
                        Logger.Info?.Print(LogClass.Application, "Loading as homebrew.");

                        try
                        {
                            if (!Device.LoadProgram(ApplicationPath))
                            {
                                Device.Dispose();

                                return false;
                            }
                        }
                        catch (ArgumentOutOfRangeException)
                        {
                            Logger.Error?.Print(
                                LogClass.Application,
                                "The specified file is not supported by Ryujinx."
                            );

                            Device.Dispose();

                            return false;
                        }

                        break;
                    }
                }
            }
            else
            {
                Logger.Warning?.Print(
                    LogClass.Application,
                    "Please specify a valid XCI/NCA/NSP/PFS0/NRO file."
                );

                Device.Dispose();

                return false;
            }

            DiscordIntegrationModule.SwitchToPlayingState(
                Device.Processes.ActiveApplication.ProgramIdText,
                Device.Processes.ActiveApplication.Name
            );

            ApplicationLibrary.LoadAndSaveMetaData(
                Device.Processes.ActiveApplication.ProgramIdText,
                appMetadata =>
                {
                    appMetadata.UpdatePreGame();
                }
            );

            return true;
        }

        internal void Resume()
        {
            Device?.System.TogglePauseEmulation(false);

            _viewModel.IsPaused = false;
            _viewModel.Title = TitleHelper.ActiveApplicationTitle(
                Device?.Processes.ActiveApplication,
                Program.Version
            );
            Logger.Info?.Print(LogClass.Emulation, "Emulation was resumed");
        }

        internal void Pause()
        {
            Device?.System.TogglePauseEmulation(true);

            _viewModel.IsPaused = true;
            _viewModel.Title = TitleHelper.ActiveApplicationTitle(
                Device?.Processes.ActiveApplication,
                Program.Version,
                LocaleManager.Instance[LocaleKeys.Paused]
            );
            Logger.Info?.Print(LogClass.Emulation, "Emulation was paused");
        }

        private void InitializeSwitchInstance()
        {
            // Initialize KeySet.
            VirtualFileSystem.ReloadKeySet();

            // Initialize Renderer.
            IRenderer renderer;

            if (
                ConfigurationState.Instance.Graphics.GraphicsBackend.Value == GraphicsBackend.Vulkan
            )
            {
                renderer = new VulkanRenderer(
                    Vk.GetApi(),
                    (RendererHost.EmbeddedWindow as EmbeddedWindowVulkan).CreateSurface,
                    VulkanHelper.GetRequiredInstanceExtensions,
                    ConfigurationState.Instance.Graphics.PreferredGpu.Value
                );
            }
            else
            {
                renderer = new OpenGLRenderer();
            }

            BackendThreading threadingMode = ConfigurationState.Instance.Graphics.BackendThreading;

            var isGALThreaded =
                threadingMode == BackendThreading.On
                || (threadingMode == BackendThreading.Auto && renderer.PreferThreading);
            if (isGALThreaded)
            {
                renderer = new ThreadedRenderer(renderer);
            }

            Logger.Info?.PrintMsg(
                LogClass.Gpu,
                $"Backend Threading ({threadingMode}): {isGALThreaded}"
            );

            // Initialize Configuration.
            var memoryConfiguration = ConfigurationState.Instance.System.ExpandRam.Value
                ? MemoryConfiguration.MemoryConfiguration6GiB
                : MemoryConfiguration.MemoryConfiguration4GiB;

            HLEConfiguration configuration =
                new(
                    VirtualFileSystem,
                    _viewModel.LibHacHorizonManager,
                    ContentManager,
                    _accountManager,
                    _userChannelPersistence,
                    renderer,
                    InitializeAudio(),
                    memoryConfiguration,
                    _viewModel.UiHandler,
                    (SystemLanguage)ConfigurationState.Instance.System.Language.Value,
                    (RegionCode)ConfigurationState.Instance.System.Region.Value,
                    ConfigurationState.Instance.Graphics.EnableVsync,
                    ConfigurationState.Instance.System.EnableDockedMode,
                    ConfigurationState.Instance.System.EnablePtc,
                    ConfigurationState.Instance.System.EnableInternetAccess,
                    ConfigurationState.Instance.System.EnableFsIntegrityChecks
                        ? IntegrityCheckLevel.ErrorOnInvalid
                        : IntegrityCheckLevel.None,
                    ConfigurationState.Instance.System.FsGlobalAccessLogMode,
                    ConfigurationState.Instance.System.SystemTimeOffset,
                    ConfigurationState.Instance.System.TimeZone,
                    ConfigurationState.Instance.System.MemoryManagerMode,
                    ConfigurationState.Instance.System.IgnoreMissingServices,
                    ConfigurationState.Instance.Graphics.AspectRatio,
                    ConfigurationState.Instance.System.AudioVolume,
                    ConfigurationState.Instance.System.UseHypervisor,
                    ConfigurationState.Instance.Multiplayer.LanInterfaceId.Value,
                    ConfigurationState.Instance.Multiplayer.Mode
                );

            Device = new Switch(configuration);
        }

        private static IHardwareDeviceDriver InitializeAudio()
        {
            var availableBackends = new List<AudioBackend>
            {
                AudioBackend.SDL2,
                AudioBackend.SoundIo,
                AudioBackend.OpenAl,
                AudioBackend.Dummy,
            };

            AudioBackend preferredBackend = ConfigurationState.Instance.System.AudioBackend.Value;

            for (int i = 0; i < availableBackends.Count; i++)
            {
                if (availableBackends[i] == preferredBackend)
                {
                    availableBackends.RemoveAt(i);
                    availableBackends.Insert(0, preferredBackend);
                    break;
                }
            }

            static IHardwareDeviceDriver InitializeAudioBackend<T>(
                AudioBackend backend,
                AudioBackend nextBackend
            )
                where T : IHardwareDeviceDriver, new()
            {
                if (T.IsSupported)
                {
                    return new T();
                }

                Logger.Warning?.Print(
                    LogClass.Audio,
                    $"{backend} is not supported, falling back to {nextBackend}."
                );

                return null;
            }

            IHardwareDeviceDriver deviceDriver = null;

            for (int i = 0; i < availableBackends.Count; i++)
            {
                AudioBackend currentBackend = availableBackends[i];
                AudioBackend nextBackend =
                    i + 1 < availableBackends.Count ? availableBackends[i + 1] : AudioBackend.Dummy;

                deviceDriver = currentBackend switch
                {
                    AudioBackend.SDL2
                        => InitializeAudioBackend<SDL2HardwareDeviceDriver>(
                            AudioBackend.SDL2,
                            nextBackend
                        ),
                    AudioBackend.SoundIo
                        => InitializeAudioBackend<SoundIoHardwareDeviceDriver>(
                            AudioBackend.SoundIo,
                            nextBackend
                        ),
                    AudioBackend.OpenAl
                        => InitializeAudioBackend<OpenALHardwareDeviceDriver>(
                            AudioBackend.OpenAl,
                            nextBackend
                        ),
                    _ => new DummyHardwareDeviceDriver(),
                };

                if (deviceDriver != null)
                {
                    ConfigurationState.Instance.System.AudioBackend.Value = currentBackend;
                    break;
                }
            }

            MainWindowViewModel.SaveConfig();

            return deviceDriver;
        }

        private void Window_BoundsChanged(object sender, Size e)
        {
            Width = (int)e.Width;
            Height = (int)e.Height;

            SetRendererWindowSize(e);
        }

        private void MainLoop()
        {
            int counter = 0;
            const int pauseAfterSteps = 20;
            // (_keyboardInterface as AvaloniaKeyboard)?.EmulateKeyPress(Key.W);
            (_mouseInterface as AvaloniaMouse)?.EmulateMousePressed(MouseButton.Button1);

            while (_isActive)
            {
                UpdateFrame();
                counter++;

                // Polling becomes expensive if it's not slept.
                Thread.Sleep(1);

                // screenshot every 20 frames
                if (counter == pauseAfterSteps)
                {
                    Task.Run(() => _renderer.Screenshot());
                    counter = 0; // Reset counter
                }
            }
        }

        private void RenderLoop()
        {
            // Invoke UI thread to set fullscreen and menu/status bar visibility
            Dispatcher.UIThread.InvokeAsync(() =>
            {
                if (_viewModel.StartGamesInFullscreen)
                {
                    _viewModel.WindowState = WindowState.FullScreen;
                }

                if (_viewModel.WindowState == WindowState.FullScreen)
                {
                    _viewModel.ShowMenuAndStatusBar = false;
                }
            });

            // Initialize renderer
            _renderer = Device.Gpu.Renderer is ThreadedRenderer tr
                ? tr.BaseRenderer
                : Device.Gpu.Renderer;

            // Subscribe to screen capture event (attach event handler ScreenCaptured event)
            _renderer.ScreenCaptured += Renderer_ScreenCapturedNoSave;

            // Initialize background context for OpenGL
            (RendererHost.EmbeddedWindow as EmbeddedWindowOpenGL)?.InitializeBackgroundContext(
                _renderer
            );

            // Initialize GPU renderer
            Device.Gpu.Renderer.Initialize(_glLogLevel);

            // Set renderer window properties
            _renderer?.Window?.SetAntiAliasing(
                (Graphics.GAL.AntiAliasing)ConfigurationState.Instance.Graphics.AntiAliasing.Value
            );
            _renderer?.Window?.SetScalingFilter(
                (Graphics.GAL.ScalingFilter)ConfigurationState.Instance.Graphics.ScalingFilter.Value
            );
            _renderer?.Window?.SetScalingFilterLevel(
                ConfigurationState.Instance.Graphics.ScalingFilterLevel.Value
            );
            _renderer?.Window?.SetColorSpacePassthrough(
                ConfigurationState.Instance.Graphics.EnableColorSpacePassthrough.Value
            );

            // Set renderer window size
            Width = (int)RendererHost.Bounds.Width;
            Height = (int)RendererHost.Bounds.Height;
            _renderer.Window.SetSize(
                (int)(Width * _topLevel.RenderScaling),
                (int)(Height * _topLevel.RenderScaling)
            );

            // Start the stopwatch for frame timing
            _chrono.Start();

            // Run the GPU renderer loop
            Device.Gpu.Renderer.RunLoop(() =>
            {
                // Set GPU thread and initialize shader cache
                Device.Gpu.SetGpuThread();
                Device.Gpu.InitializeShaderCache(_gpuCancellationTokenSource.Token);

                // Change VSync mode
                _renderer.Window.ChangeVSyncMode(Device.EnableDeviceVsync);

                // Main rendering loop
                while (_isActive)
                {
                    _ticks += _chrono.ElapsedTicks;
                    _chrono.Restart();

                    // Process frame if FIFO is ready
                    if (Device.WaitFifo())
                    {
                        Device.Statistics.RecordFifoStart();
                        Device.ProcessFrame();
                        Device.Statistics.RecordFifoEnd();
                    }

                    // Present frame if available
                    while (Device.ConsumeFrameAvailable())
                    {
                        if (!_renderingStarted)
                        {
                            _renderingStarted = true;
                            _viewModel.SwitchToRenderer(false);
                            InitStatus();
                        }

                        Device.PresentFrame(
                            () =>
                                (RendererHost.EmbeddedWindow as EmbeddedWindowOpenGL)?.SwapBuffers()
                        );
                    }

                    // Update status if enough ticks have passed
                    if (_ticks >= _ticksPerFrame)
                    {
                        UpdateStatus();
                    }
                }

                // Flush threaded commands if using threaded renderer
                if (Device.Gpu.Renderer is ThreadedRenderer threaded)
                {
                    threaded.FlushThreadedCommands();
                }

                // Signal that GPU is done
                _gpuDoneEvent.Set();
            });

            // Make the OpenGL context current
            (RendererHost.EmbeddedWindow as EmbeddedWindowOpenGL)?.MakeCurrent(true);
        }

        public void InitStatus()
        {
            StatusInitEvent?.Invoke(
                this,
                new StatusInitEventArgs(
                    ConfigurationState.Instance.Graphics.GraphicsBackend.Value switch
                    {
                        GraphicsBackend.Vulkan => "Vulkan",
                        GraphicsBackend.OpenGl => "OpenGL",
                        _ => throw new NotImplementedException()
                    },
                    $"GPU: {_renderer.GetHardwareInfo().GpuDriver}"
                )
            );
        }

        public void UpdateStatus()
        {
            // Run a status update only when a frame is to be drawn. This prevents from updating the ui and wasting a render when no frame is queued.
            string dockedMode = ConfigurationState.Instance.System.EnableDockedMode
                ? LocaleManager.Instance[LocaleKeys.Docked]
                : LocaleManager.Instance[LocaleKeys.Handheld];

            if (GraphicsConfig.ResScale != 1)
            {
                dockedMode += $" ({GraphicsConfig.ResScale}x)";
            }

            StatusUpdatedEvent?.Invoke(
                this,
                new StatusUpdatedEventArgs(
                    Device.EnableDeviceVsync,
                    LocaleManager.Instance[LocaleKeys.VolumeShort]
                        + $": {(int)(Device.GetVolume() * 100)}%",
                    dockedMode,
                    ConfigurationState.Instance.Graphics.AspectRatio.Value.ToText(),
                    LocaleManager.Instance[LocaleKeys.Game]
                        + $": {Device.Statistics.GetGameFrameRate():00.00} FPS ({Device.Statistics.GetGameFrameTime():00.00} ms)",
                    $"FIFO: {Device.Statistics.GetFifoPercent():00.00} %"
                )
            );
        }

        public async Task ShowExitPrompt()
        {
            bool shouldExit = !ConfigurationState.Instance.ShowConfirmExit;
            if (!shouldExit)
            {
                if (_dialogShown)
                {
                    return;
                }

                _dialogShown = true;

                shouldExit = await ContentDialogHelper.CreateStopEmulationDialog();

                _dialogShown = false;
            }

            if (shouldExit)
            {
                Stop();
            }
        }

        private bool UpdateFrame()
        {
            // Check if the application is active
            if (!_isActive)
            {
                return false;
            }

            // Update NpadManager with the current aspect ratio
            NpadManager.Update(ConfigurationState.Instance.Graphics.AspectRatio.Value.ToFloat());

            // Check if the view model is active
            if (_viewModel.IsActive)
            {
                bool isCursorVisible = true;

                // Determine cursor visibility based on configuration and cursor state
                if (_isCursorInRenderer && !_viewModel.ShowLoadProgress)
                {
                    if (ConfigurationState.Instance.Hid.EnableMouse.Value)
                    {
                        isCursorVisible =
                            ConfigurationState.Instance.HideCursor.Value == HideCursorMode.Never;
                    }
                    else
                    {
                        isCursorVisible =
                            ConfigurationState.Instance.HideCursor.Value == HideCursorMode.Never
                            || (
                                ConfigurationState.Instance.HideCursor.Value
                                    == HideCursorMode.OnIdle
                                && Stopwatch.GetTimestamp() - _lastCursorMoveTime
                                    < CursorHideIdleTime * Stopwatch.Frequency
                            );
                    }
                }

                // Update cursor state if it has changed
                if (
                    _cursorState
                    != (
                        isCursorVisible ? CursorStates.CursorIsVisible : CursorStates.CursorIsHidden
                    )
                )
                {
                    if (isCursorVisible)
                    {
                        ShowCursor();
                        // _renderer.Screenshot(); // screenshot is saved each tiem cursor moves out of the window
                    }
                    else
                    {
                        HideCursor();
                    }
                }

                // Handle keyboard input for deleting disk cache load state
                Dispatcher.UIThread.Post(() =>
                {
                    if (
                        _keyboardInterface.GetKeyboardStateSnapshot().IsPressed(Key.Delete)
                        && _viewModel.WindowState != WindowState.FullScreen
                    )
                    {
                        Device.Processes.ActiveApplication.DiskCacheLoadState?.Cancel();
                    }
                });

                // Get the current hotkey state
                KeyboardHotkeyState currentHotkeyState = GetHotkeyState();

                // Handle hotkey state changes
                if (currentHotkeyState != _prevHotkeyState)
                {
                    switch (currentHotkeyState)
                    {
                        case KeyboardHotkeyState.ToggleVSync:
                            ToggleVSync();
                            break;
                        case KeyboardHotkeyState.Screenshot:
                            ScreenshotRequested = true;
                            break;
                        case KeyboardHotkeyState.ShowUI:
                            _viewModel.ShowMenuAndStatusBar = !_viewModel.ShowMenuAndStatusBar;
                            break;
                        case KeyboardHotkeyState.Pause:
                            if (_viewModel.IsPaused)
                            {
                                Resume();
                            }
                            else
                            {
                                Pause();
                            }
                            break;
                        case KeyboardHotkeyState.ToggleMute:
                            if (Device.IsAudioMuted())
                            {
                                Device.SetVolume(_viewModel.VolumeBeforeMute);
                            }
                            else
                            {
                                _viewModel.VolumeBeforeMute = Device.GetVolume();
                                Device.SetVolume(0);
                            }

                            _viewModel.Volume = Device.GetVolume();
                            break;
                        case KeyboardHotkeyState.ResScaleUp:
                            GraphicsConfig.ResScale =
                                GraphicsConfig.ResScale % MaxResolutionScale + 1;
                            break;
                        case KeyboardHotkeyState.ResScaleDown:
                            GraphicsConfig.ResScale =
                                (MaxResolutionScale + GraphicsConfig.ResScale - 2)
                                    % MaxResolutionScale
                                + 1;
                            break;
                        case KeyboardHotkeyState.VolumeUp:
                            _newVolume = MathF.Round((Device.GetVolume() + VolumeDelta), 2);
                            Device.SetVolume(_newVolume);

                            _viewModel.Volume = Device.GetVolume();
                            break;
                        case KeyboardHotkeyState.VolumeDown:
                            _newVolume = MathF.Round((Device.GetVolume() - VolumeDelta), 2);
                            Device.SetVolume(_newVolume);

                            _viewModel.Volume = Device.GetVolume();
                            break;
                        case KeyboardHotkeyState.None:
                            (_keyboardInterface as AvaloniaKeyboard).Clear();
                            break;
                    }
                }

                // Update the previous hotkey state
                _prevHotkeyState = currentHotkeyState;

                // Handle screenshot request
                if (ScreenshotRequested)
                {
                    ScreenshotRequested = false;
                    _renderer.Screenshot();
                }
            }

            // Handle touchscreen input
            bool hasTouch = false;

            if (_viewModel.IsActive && !ConfigurationState.Instance.Hid.EnableMouse.Value)
            {
                hasTouch = TouchScreenManager.Update(
                    true,
                    (_inputManager.MouseDriver as AvaloniaMouseDriver).IsButtonPressed(
                        MouseButton.Button1
                    ),
                    ConfigurationState.Instance.Graphics.AspectRatio.Value.ToFloat()
                );
            }

            // Update touchscreen if no touch input is detected
            if (!hasTouch)
            {
                Device.Hid.Touchscreen.Update();
            }

            // Update debug pad
            Device.Hid.DebugPad.Update();

            return true;
        }

        private KeyboardHotkeyState GetHotkeyState()
        {
            KeyboardHotkeyState state = KeyboardHotkeyState.None;

            if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.ToggleVsync
                )
            )
            {
                state = KeyboardHotkeyState.ToggleVSync;
            }
            else if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.Screenshot
                )
            )
            {
                state = KeyboardHotkeyState.Screenshot;
            }
            else if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.ShowUI
                )
            )
            {
                state = KeyboardHotkeyState.ShowUI;
            }
            else if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.Pause
                )
            )
            {
                state = KeyboardHotkeyState.Pause;
            }
            else if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.ToggleMute
                )
            )
            {
                state = KeyboardHotkeyState.ToggleMute;
            }
            else if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.ResScaleUp
                )
            )
            {
                state = KeyboardHotkeyState.ResScaleUp;
            }
            else if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.ResScaleDown
                )
            )
            {
                state = KeyboardHotkeyState.ResScaleDown;
            }
            else if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.VolumeUp
                )
            )
            {
                state = KeyboardHotkeyState.VolumeUp;
            }
            else if (
                _keyboardInterface.IsPressed(
                    (Key)ConfigurationState.Instance.Hid.Hotkeys.Value.VolumeDown
                )
            )
            {
                state = KeyboardHotkeyState.VolumeDown;
            }

            return state;
        }
    }
}
