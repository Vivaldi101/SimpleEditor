
/////////////////////////
// TODO: Hone and refine the gap buffer invariants!!!!!!!
// TODO: Remove the globals.
// TODO: One megastruct.
/////////////////////////

#include <assert.h>
#include <stdint.h>
#include <Windows.h>
#include <d2d1.h>
#include <dwrite.h>
#include <malloc.h>

#pragma comment(lib, "dwrite.lib")
#pragma comment(lib, "d2d1.lib")

#define global static
#define local static
#define function static

#define Cast(x, t) (t)(x)
#define ZeroStruct(x) memset((x), 0, sizeof(*(x)));
#define ArrayCount(a) sizeof((a)) / sizeof((*a))

#define PreCondition(a) if(!(a)) __debugbreak();
#define PostCondition(a) if(!(a)) __debugbreak();
#define Invariant(a) if(!(a)) __debugbreak();
#define Implies(a, b) Invariant(!(a) || (b))

typedef unsigned char byte;

typedef int8_t s8;
typedef int16_t s16;
typedef int32_t s32;
typedef int64_t s64;

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef u32 b32;
typedef float f32;

static bool GlobalQuit;

// Test globals.
ID2D1Factory *GlobalD2D1Factory;
IDWriteFactory *GlobalWriteFactory;
ID2D1HwndRenderTarget *GlobalRenderTarget;
IDWriteTextFormat *GlobalTextFormat;
ID2D1SolidColorBrush* GlobalTextBrush;


typedef s64 buffer_position;
typedef s64 cursor_position;

struct gap_buffer
{
	byte *Memory;
	buffer_position GapBegin;
	buffer_position GapEnd;
	buffer_position End;	
	cursor_position Cursor;
};

function void
GapBufferInvariants(gap_buffer *Buffer)
{
	Invariant(Buffer->Cursor >= 0);
	Invariant(Buffer->GapBegin >= 0);

	Invariant(Buffer->Cursor <= Buffer->End);
	Invariant(Buffer->GapBegin <= Buffer->GapEnd);
	Invariant(Buffer->GapEnd <= Buffer->End);
}

#define GapSize(Buffer) ((Buffer)->GapEnd - (Buffer)->GapBegin)
#define IsGapFull(Buffer) GapSize((Buffer)) == 0

function void
MoveBytes(byte *Destination, byte *Source, u64 Size)
{
	memmove(Destination, Source, Size);
}

function void
SetBytes(byte *Destination, int Value, u64 Size)
{
	memset(Destination, Value, Size);
}

function void
CopyBytes(byte *Destination, byte *Source, u64 Size)
{
	// TODO: Overlap conditions.
	memcpy(Destination, Source, Size);
}

function void 
Initialize(gap_buffer *Buffer, size_t Size)
{
	PreCondition(Buffer);
	PreCondition(IsGapFull(Buffer));
	PreCondition(Size != 1);
	GapBufferInvariants(Buffer);

	Buffer->GapBegin = Buffer->GapEnd = Buffer->End = 0;
	Buffer->Memory = Cast(HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, Size), byte*);
	Buffer->End = Size - 1;
	Buffer->GapBegin = 0;
	Buffer->GapEnd = Buffer->End;

	PostCondition(!IsGapFull(Buffer));
	PostCondition(Buffer->Memory);
	GapBufferInvariants(Buffer);
}

/*
	wp(end = size - 1; begin = 0, end - begin != 0)
	wp(end = size - 1, , end - 0 != 0)
	= (size - 1 - 0 != 0)
	= (size - 1 != 0)
	= (size != 1)

	wp(end = size - 1; begin = 0, end != begin)
	wp(end = size - 1, end != 0)
	= (size - 1 != 0)
	= (size != 1)
*/


function void
InsertCharacter(gap_buffer *Buffer, char Char)
{
	PreCondition(Buffer);
	GapBufferInvariants(Buffer);

	// Needs to expand the gap for the new reallocated buffer.
	if(IsGapFull(Buffer))
	{
		buffer_position NewBufferSize = (Buffer->End + 1) * 2;
		buffer_position NewGapSize = NewBufferSize / 2;

		Buffer->Memory = Cast(HeapReAlloc(GetProcessHeap(), 0, Buffer->Memory, NewBufferSize), byte*);

		Buffer->GapEnd = Buffer->GapBegin + NewGapSize - 1;
		Buffer->End = NewBufferSize - 1;

		PostCondition(NewBufferSize == (NewGapSize * 2));
	}

	Buffer->Memory[Buffer->GapBegin] = Char;
	Buffer->GapBegin++;
	Buffer->Cursor++;

	GapBufferInvariants(Buffer);
}

function void
InsertNewline(gap_buffer *Buffer)
{
	GapBufferInvariants(Buffer);
	Buffer->Memory[Buffer->GapBegin] = '\n';
	Buffer->GapBegin++;
	Buffer->Cursor = 0;
	GapBufferInvariants(Buffer);
}

// Fix the size of the cursor to match font size.
// Fix the line alignment.
function void
DrawCursor(gap_buffer *Buffer, buffer_position CursorLeft, buffer_position CursorTop)
{
	D2D1_RECT_F Cursor;
	const f32 CursorWidth = 20.0f;
	const f32 CursorHeight = 40.0f;
	Cursor.left = CursorLeft*CursorWidth;
	Cursor.top = CursorTop*CursorHeight;
	Cursor.right = Cursor.left + CursorWidth;
	Cursor.bottom = Cursor.top + CursorHeight;

	D2D1_COLOR_F OldColor = GlobalTextBrush->GetColor();
	D2D1_COLOR_F CursorColor = {1.0f, 0.0f, 0.0f, 1.0f};
	GlobalTextBrush->SetColor(&CursorColor);
	GlobalRenderTarget->DrawRectangle(Cursor, GlobalTextBrush, 2.0f);
	GlobalTextBrush->SetColor(&OldColor);
}

function void
Draw(gap_buffer *Buffer, f32 Left, f32 Top, f32 Width, f32 Height)
{
	byte Utf8[256];
	ZeroMemory(Utf8, sizeof(Utf8));
	WCHAR Utf16[256];
	ZeroMemory(Utf16, sizeof(Utf16));
	D2D1_RECT_F Layout;
	Layout.left = Left;
	Layout.top = Top;
	Layout.right = Layout.left + Width;
	Layout.bottom = Layout.top + Height;

	GapBufferInvariants(Buffer);

	buffer_position GapBegin = Buffer->GapBegin;
	buffer_position Cursor = Buffer->Cursor;
	buffer_position Line = 0;

	// TODO: Handle multibyte unicode advancements and new lines.
	// TODO: Optimize.
	for (buffer_position i = 0; i < GapBegin; ++i)
	{
		CopyBytes(Utf8 + i, Buffer->Memory + i, 1);
		MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)Utf8 + i, 1, Utf16 + i, sizeof(Utf16));
		if (Utf8[i] == '\n')
		{
			Line++;
		}
	}

	DrawCursor(Buffer, Cursor, Line);

	GlobalRenderTarget->DrawText(Utf16, (UINT)wcslen(Utf16), GlobalTextFormat, Layout, GlobalTextBrush);
	GapBufferInvariants(Buffer);
}

LRESULT CALLBACK
SysWindowProc(HWND Window, UINT Message, WPARAM WParam, LPARAM LParam)
{
	LRESULT Result = 0;

	gap_buffer* GapBuffer = (gap_buffer*)(void*)GetWindowLongPtr(Window, GWLP_USERDATA);

	if (GapBuffer)
	{
		switch (Message)
		{
		case WM_DESTROY:
			{
				GlobalQuit = true;
			} break;
		case WM_SIZE:
			{
				RECT ClientRect;
				GetClientRect(Window, &ClientRect);
				D2D1_SIZE_U WindowSize;
				WindowSize.width = ClientRect.right - ClientRect.left;
				WindowSize.height = ClientRect.bottom - ClientRect.top;
				if (GlobalRenderTarget)
				{
					GlobalRenderTarget->Release();
				}
				GlobalD2D1Factory->CreateHwndRenderTarget(D2D1::RenderTargetProperties(), D2D1::HwndRenderTargetProperties(Window, WindowSize), &GlobalRenderTarget);
				if (GlobalTextBrush)
				{
					GlobalTextBrush->Release();
				}
				GlobalRenderTarget->CreateSolidColorBrush(D2D1::ColorF(D2D1::ColorF::Black), &GlobalTextBrush);
			} break;
		case WM_CHAR:
			{
				u32 VkCode = (u32)WParam;
				b32 WasDown = (LParam & (1 << 30)) != 0;
				b32 IsDown = (LParam & (1 << 31)) == 0;

				//if (WasDown != IsDown)
				{
					if (VkCode == 0x0d)
					{
						//Backspace(GlobalZedBuffer);
						InsertNewline(GapBuffer);
					}
					else if (VkCode == VK_BACK)
					{
						//Backspace(GlobalZedBuffer);
					}
					else if (VkCode == 'x')
					{
						//Delete(GlobalZedBuffer);
					}
					else if (VkCode == 'J')
					{
						//MoveBackwards(GlobalZedBuffer);
					}
					else if (VkCode == 'K')
					{
						//MoveForwards(GlobalZedBuffer);
					}
					else
					{
						// Cleanup
						{
							int BufferSize = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&WParam, 1, 0, 0, 0, 0);

							char* Buffer = (char*)_malloca(BufferSize);

							int Result = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&WParam, 1, Buffer, BufferSize, 0, 0);

							// Remove the <= 2 byte assumption.
							// Multibyte chars.
							if (Result == 2)
							{
								InsertCharacter(GapBuffer, Buffer[0]);
								InsertCharacter(GapBuffer, Buffer[1]);
							}
							else if (Result == 1)
							{
								InsertCharacter(GapBuffer, Buffer[0]);
							}
						}
					}
				}
			} break;
		default:
			{
				Result = DefWindowProc(Window, Message, WParam, LParam);
				break;
			}
		}
		return Result;
	}

	return DefWindowProc(Window, Message, WParam, LParam);
}

int WINAPI 
WinMain(HINSTANCE Instance, HINSTANCE, LPSTR, int)
{
	gap_buffer GapBuffer = {};
	Initialize(&GapBuffer, 256);

	// Stupid dwrite COM shit.
	{
		HRESULT DWriteResult = D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED, &GlobalD2D1Factory);
		DWriteResult = DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED, __uuidof(IDWriteFactory), (IUnknown**)&GlobalWriteFactory);
		DWriteResult = GlobalWriteFactory->CreateTextFormat(L"Consolas", 0, DWRITE_FONT_WEIGHT_REGULAR, DWRITE_FONT_STYLE_NORMAL, DWRITE_FONT_STRETCH_NORMAL, 36.0f, L"en-us", &GlobalTextFormat );
		GlobalTextFormat->SetWordWrapping(DWRITE_WORD_WRAPPING_NO_WRAP);
	}

	WNDCLASS WindowClass = {};
	//WindowClass.cbWndExtra = sizeof(GapBuffer);
	WindowClass.hInstance = Instance;
	WindowClass.lpfnWndProc = SysWindowProc;
	WindowClass.lpszClassName = L"zed";
	WindowClass.style = CS_OWNDC | CS_HREDRAW | CS_VREDRAW;
	ATOM WindowClassAtom = RegisterClass(&WindowClass);

	Invariant(WindowClassAtom);

	// Adjust the client area related to the screen origin + client size.
	RECT DesiredWindow = { 500, 300, 800, 600 };
	AdjustWindowRect(&DesiredWindow, WS_OVERLAPPEDWINDOW, FALSE);
	HWND WindowHandle = CreateWindow(L"zed", L"Editor", WS_OVERLAPPEDWINDOW, DesiredWindow.left, DesiredWindow.top, DesiredWindow.right, DesiredWindow.bottom, 0, 0, Instance, 0);

	Invariant(WindowHandle);

	SetWindowLongPtr(WindowHandle, GWLP_USERDATA, (LONG_PTR)&GapBuffer);

	UpdateWindow(WindowHandle);
	ShowWindow(WindowHandle, SW_SHOW);

	while (!GlobalQuit)
	{
		MSG Message;
		while (PeekMessage(&Message, 0, 0, 0, PM_REMOVE))
		{
			TranslateMessage(&Message);
			DispatchMessage(&Message);
		}
		// TODO: Cap to 60FPS.
		GlobalRenderTarget->BeginDraw();
		GlobalRenderTarget->Clear(D2D1::ColorF(D2D1::ColorF::White));
		Draw(&GapBuffer, 0, 0, 800, 600);
		//DrawCursor(GlobalZedBuffer);
		GlobalRenderTarget->EndDraw();
	}

	return 0;
}