using System;
using static SDL2.SDL;

namespace Ryujinx.Input.SDL2
{
    public class KeyboardEmulator
    {
        private IntPtr _window;
        private IntPtr _sdlContext;

        // Modify the constructor to accept an existing window handle
        public KeyboardEmulator(IntPtr existingWindow)
        {
            _window = existingWindow; // Use the existing window handle
            if (SDL_Init(SDL_INIT_VIDEO) < 0)
            {
                Console.WriteLine("SDL could not initialize! SDL_Error: " + SDL_GetError());
            }
            else
            {
                _sdlContext = SDL_GL_CreateContext(_window);
                if (_sdlContext == IntPtr.Zero)
                {
                    Console.WriteLine(
                        "GL context could not be created! SDL_Error: " + SDL_GetError()
                    );
                }
            }
        }

        public void EmulateKeyPress(SDL_Keycode key)
        {
            SDL_Event sdlEvent = new SDL_Event
            {
                type = SDL_EventType.SDL_KEYDOWN,
                key = new SDL_KeyboardEvent
                {
                    keysym = new SDL_Keysym
                    {
                        sym = key,
                        mod = SDL_Keymod.KMOD_NONE,
                        scancode = SDL_GetScancodeFromKey(key)
                    }
                }
            };

            SDL_PushEvent(ref sdlEvent);
            Console.WriteLine($"Emulated key press: {key}");
        }

        public void EmulateKeyRelease(SDL_Keycode key)
        {
            SDL_Event sdlEvent = new SDL_Event
            {
                type = SDL_EventType.SDL_KEYUP,
                key = new SDL_KeyboardEvent
                {
                    keysym = new SDL_Keysym
                    {
                        sym = key,
                        mod = SDL_Keymod.KMOD_NONE,
                        scancode = SDL_GetScancodeFromKey(key)
                    }
                }
            };

            SDL_PushEvent(ref sdlEvent);
            Console.WriteLine($"Emulated key release: {key}");
        }

        public void Cleanup()
        {
            SDL_GL_DeleteContext(_sdlContext);
            SDL_Quit();
        }
    }
}
