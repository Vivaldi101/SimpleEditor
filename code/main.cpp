
/////////////////////////
// TODO: Remove the globals.
/////////////////////////

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
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
#define Halt __debugbreak();

#ifdef _DEBUG

#define Pre(a) if(!(a)) Halt
#define Post(a) if(!(a)) Halt
#define Invariant(a) if(!(a)) Halt
#define Implies(a, b) Invariant(!(a) || (b))

#else

#define Pre(a)
#define Post(a)
#define Invariant(a)
#define Implies(a, b)

#endif

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
static ID2D1Factory *GlobalD2D1Factory;
static IDWriteFactory *GlobalWriteFactory;
static ID2D1HwndRenderTarget *GlobalRenderTarget;
static IDWriteTextFormat *GlobalTextFormat;
static ID2D1SolidColorBrush* GlobalTextBrush;

typedef u64 buffer_position;
typedef u64 cursor_position;

struct gap_buffer
{
	buffer_position GapBegin;
	buffer_position GapEnd;
	buffer_position End;	
	cursor_position Cursor;
	byte *Memory;

	byte Reserved[24];	// Align to 64 byte cache line.
};

// Post and precondition for gap size staying same.

#define GapSize(Buffer) ((Buffer)->GapEnd - (Buffer)->GapBegin)
#define IsGapFull(Buffer) (GapSize((Buffer)) == 0)
#define BufferSize(Buffer) ((Buffer)->End - GapSize(Buffer))
#define IsCursorInGapExcl(Buffer) ((Buffer)->GapBegin < (Buffer)->Cursor && (Buffer)->Cursor < (Buffer)->GapEnd)

//#define CursorPoint(Buffer) (((Buffer)->Cursor > (Buffer)->GapBegin + 1) ? (Buffer)->Cursor -= GapSize((Buffer)) : (Buffer)->Cursor)
#define CursorPoint(Buffer) 

#ifdef _DEBUG
function void
DebugMessage(const char* format, ...)
{
	char Temp[1024];
	va_list Args;
	va_start(Args, format);
	wvsprintfA(Temp, format, Args);
	va_end(Args);
	OutputDebugStringA(Temp);
}
#else
function void
DebugMessage(const char* format, ...) {}
#endif

function void
GapBufferInvariants(gap_buffer *Buffer)
{
	Invariant(Buffer->Cursor <= Buffer->End);
	Invariant(Buffer->Cursor <= BufferSize(Buffer));

	Invariant(Buffer->GapBegin <= Buffer->GapEnd);
	Invariant(Buffer->GapEnd <= Buffer->End);
}

function bool
IsNonNullAscii(char C)
{
	return isascii(C) && C != '\0';
}

function void
MoveBytes(byte *Destination, byte *Source, u64 Size)
{
	MoveMemory(Destination, Source, Size);
}

function void
SetBytes(byte *Destination, int Value, u64 Size)
{
	FillMemory(Destination, Size, Value);
}

function void
CopyBytes(byte *Destination, byte *Source, u64 Size)
{
	CopyMemory(Destination, Source, Size);
}

function void 
DeInitialize(gap_buffer* Buffer)
{
	GapBufferInvariants(Buffer);
	Pre(Buffer);

	// Test return values.
	HeapFree(GetProcessHeap(), HEAP_ZERO_MEMORY, Buffer->Memory);
}

function void 
Initialize(gap_buffer *Buffer, size_t Size)
{
	GapBufferInvariants(Buffer);
	Pre(Buffer);
	Pre(IsGapFull(Buffer));
	Pre(Size != 1);

	Buffer->GapBegin = Buffer->GapEnd = Buffer->End = 0;
	Buffer->Memory = Cast(HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, Size), byte*);
	Buffer->End = Size - 1;
	Buffer->GapBegin = 0;
	Buffer->Cursor = 0;
	Buffer->GapEnd = Buffer->End;

	Post(!IsGapFull(Buffer));
	Post(Buffer->Memory);
	GapBufferInvariants(Buffer);
}

function bool
TryInsertCharacter(gap_buffer *Buffer, char Char)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	if(IsGapFull(Buffer))	// gap begin == gap end
	{
		Pre(Buffer->GapBegin == Buffer->GapEnd);

		const buffer_position OldEnd = Buffer->End;
		const buffer_position OldGapEnd = Buffer->GapEnd;
		const buffer_position OldGapBegin = Buffer->GapBegin;
		const buffer_position OldBufferSize = BufferSize(Buffer);
		const buffer_position BufferRemnants = OldEnd - OldGapEnd;

		const buffer_position NewBufferSize = BufferSize(Buffer) * 2 + OldGapEnd + BufferRemnants;
		const buffer_position NewGapSize = NewBufferSize / 2;

		const void* RealloctedMemory = Cast(HeapReAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, Buffer->Memory, NewBufferSize), byte*);

		if (!RealloctedMemory)
		{
			DeInitialize(Buffer);

			return false;
		}

		Buffer->Memory = (byte*)RealloctedMemory;

		Buffer->End = NewBufferSize - 1;
		Buffer->GapEnd = Buffer->End - BufferRemnants;

		// Shuffle the characters after the previous gap after new gap end.
		MoveBytes(Buffer->Memory + Buffer->GapEnd + 1, Buffer->Memory + OldGapBegin + 1, OldEnd - OldGapEnd);

		//Post(NewBufferSize == (NewGapSize * 2));

		// Gap is at the end of the new buffer.
		Post(Buffer->GapBegin != Buffer->GapEnd);

		// Make sure old buffer remnants fit after the gap.
		Post(Buffer->GapEnd == Buffer->End - BufferRemnants);

		//Post(BufferSize(Buffer) == GapSize(Buffer) + OldGapBegin + BufferRemnants);
	}

	Buffer->Memory[Buffer->GapBegin] = Char;
	Buffer->Cursor++;

	CursorPoint(Buffer);

	Buffer->GapBegin++;

	GapBufferInvariants(Buffer);

	return true;
}

function void
InsertNewline(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	TryInsertCharacter(Buffer, '\n');

	GapBufferInvariants(Buffer);
}

function void
MoveForwards(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	if (Buffer->GapEnd == Buffer->End)
	{
		return;
	}

	MoveBytes(Buffer->Memory + Buffer->GapBegin, Buffer->Memory + Buffer->GapEnd + 1, 1);
	Buffer->Cursor++;

	CursorPoint(Buffer);

	Buffer->GapBegin++;
	Buffer->GapEnd++;
	//CursorPoint(Buffer);

	GapBufferInvariants(Buffer);
}

function void
MoveBackwards(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	if (Buffer->GapBegin == 0)
	{
		return;
	}

	MoveBytes(Buffer->Memory + Buffer->GapEnd, Buffer->Memory + Buffer->GapBegin - 1, 1);
	Buffer->Cursor--;

	CursorPoint(Buffer);

	Buffer->GapEnd--;
	Buffer->GapBegin--;

	GapBufferInvariants(Buffer);
}

// Fix similarly to moving backwards.
function void
Backspace(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	// Cant backspace anymore.
	if (Buffer->GapBegin == 0)
	{
		return;
	}

	Buffer->Cursor--;
	CursorPoint(Buffer);

	Buffer->GapBegin--;

	GapBufferInvariants(Buffer);
}

// Fix the size of the cursor to match font size.
// Fix the line alignment.
function void
DrawCursor(f32 CursorLeft, f32 CursorTop, f32 CursorRight, f32 CursorBottom)
{
	D2D1_RECT_F Cursor;

	Cursor.left = CursorLeft;
	Cursor.top = CursorTop;
	Cursor.right = CursorRight;
	Cursor.bottom = CursorBottom;

	D2D1_COLOR_F OldColor = GlobalTextBrush->GetColor();
	D2D1_COLOR_F CursorColor = {1.0f, 0.0f, 0.0f, 1.0f};
	GlobalTextBrush->SetColor(&CursorColor);
	GlobalRenderTarget->DrawRectangle(Cursor, GlobalTextBrush, 2.0f);
	GlobalTextBrush->SetColor(&OldColor);
}

function void
Draw(gap_buffer *Buffer, f32 Left, f32 Top, f32 Width, f32 Height)
{
	const size_t UtfBufferSize = 512;
	byte Utf8[UtfBufferSize];
	ZeroMemory(Utf8, sizeof(Utf8));
	WCHAR Utf16[UtfBufferSize];
	ZeroMemory(Utf16, sizeof(Utf16));

	D2D1_RECT_F Layout = {};
	Layout.left = Left;
	Layout.top = Top;
	Layout.right = Layout.left + Width;
	Layout.bottom = Layout.top + Height;

	GapBufferInvariants(Buffer);

	buffer_position GapBegin = Buffer->GapBegin;
	buffer_position GapEnd = Buffer->GapEnd;
	buffer_position End = Buffer->End;
	buffer_position Lines = 0;
	buffer_position UtfIndex = 0;

	// TODO: Handle multibyte unicode advancements and new lines.
	// TODO: Optimize.

	Invariant(UtfIndex <= ArrayCount(Utf8) && UtfIndex <= ArrayCount(Utf16));
	for (buffer_position i = 0; i < GapBegin && UtfIndex != UtfBufferSize; ++i)
	{
		if (!IsNonNullAscii(Buffer->Memory[i]))
		{
			continue;
		}

		CopyBytes(Utf8 + UtfIndex, Buffer->Memory + i, 1);
		MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)Utf8 + UtfIndex, 1, Utf16 + UtfIndex, sizeof(Utf16));
		UtfIndex++;
		if (Utf8[i] == '\n')
		{
			Lines++;
		}
		Invariant(UtfIndex <= ArrayCount(Utf8) && UtfIndex <= ArrayCount(Utf16));
	}

	for (buffer_position i = GapEnd + 1; i <= End && UtfIndex != UtfBufferSize; ++i)
	{
		if (!IsNonNullAscii(Buffer->Memory[i]))
		{
			continue;
		}

		CopyBytes(Utf8 + UtfIndex, Buffer->Memory + i, 1);
		MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)Utf8 + UtfIndex, 1, Utf16 + UtfIndex, sizeof(Utf16));
		UtfIndex++;
		if (Utf8[i] == '\n')
		{
			Lines++;
		}
		Invariant(UtfIndex <= ArrayCount(Utf8) && UtfIndex <= ArrayCount(Utf16));
	}

	Invariant(UtfIndex <= ArrayCount(Utf8) && UtfIndex <= ArrayCount(Utf16));

	Pre(ArrayCount(Utf16) > 0);
	Utf16[ArrayCount(Utf16) - 1] = 0;

	GlobalRenderTarget->PushAxisAlignedClip(&Layout, D2D1_ANTIALIAS_MODE_ALIASED);

	IDWriteTextLayout* TextLayout;
	GlobalWriteFactory->CreateTextLayout(Utf16, (UINT)wcslen(Utf16), GlobalTextFormat, Layout.right - Layout.left, Layout.bottom - Layout.top, &TextLayout);

	Pre(TextLayout);
	GlobalRenderTarget->DrawTextLayout(D2D1::Point2F(Layout.left, Layout.top), TextLayout, GlobalTextBrush);

	DWRITE_LINE_METRICS LineMetrics;
	UINT32 LineCount;
	TextLayout->GetLineMetrics(&LineMetrics, (u32)Lines, &LineCount);

	f32 CursorX, CursorY;
	DWRITE_HIT_TEST_METRICS CursorMetrics;
	TextLayout->HitTestTextPosition((u32)Buffer->Cursor, FALSE, &CursorX, &CursorY, &CursorMetrics);

	f32 CursorLeft = CursorX + Layout.left;
	f32 CursorTop = CursorY + Layout.top;
	f32 CursorRight = CursorLeft + CursorMetrics.width;
	f32 CursorBottom = CursorTop + CursorMetrics.height;

	DrawCursor(CursorLeft, CursorTop, CursorRight, CursorBottom);

	DebugMessage("Cursor position: \t%d\n", Buffer->Cursor);
	DebugMessage("Buffer size: \t\t%d\n", BufferSize(Buffer));
	//DebugMessage("Buffer gap: \t\t%d\n", GapSize(Buffer));

	GlobalRenderTarget->PopAxisAlignedClip();

	GapBufferInvariants(Buffer);
}

LRESULT CALLBACK
SysWindowProc(HWND Window, UINT Message, WPARAM WParam, LPARAM LParam)
{
	LRESULT Result = 0;

	gap_buffer* Buffer = (gap_buffer*)(void*)GetWindowLongPtr(Window, GWLP_USERDATA);

	if (Buffer)
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
				{
					u32 VkCode = (u32)WParam;
					b32 WasDown = (LParam & (1ll << 30)) != 0;
					b32 IsDown = (LParam & (1ll << 31)) == 0;

					if (VkCode == 0x0d)
					{
						InsertNewline(Buffer);
					}
					else if (VkCode == VK_BACK)
					{
						Backspace(Buffer);
					}
					else if (VkCode == 'x')
					{
						//Delete(GlobalZedBuffer);
					}
					else if (VkCode == 'J')
					{
						MoveBackwards(Buffer);
					}
					else if (VkCode == 'K')
					{
						MoveForwards(Buffer);
					}
					else
					{
						// Cleanup
						{
							const int BufferSize = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&WParam, 1, 0, 0, 0, 0);

							char* MultiBytes = (char*)_malloca(BufferSize);

							if (!Buffer)
							{
								break;
							}

							const int Result = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&WParam, 1, MultiBytes, BufferSize, 0, 0);

							// Remove the <= 2 byte assumption.
							// Multibyte chars.
							// TODO: test the booleans.
							if (Result == 2)
							{
								TryInsertCharacter(Buffer, MultiBytes[0]);
								TryInsertCharacter(Buffer, MultiBytes[1]);
							}
							else if (Result == 1)
							{
								TryInsertCharacter(Buffer, MultiBytes[0]);
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
	Initialize(&GapBuffer, 4096);

	// Stupid dwrite COM shit.
	{
		HRESULT DWriteResult = D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED, &GlobalD2D1Factory);
		DWriteResult = DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED, __uuidof(IDWriteFactory), (IUnknown**)&GlobalWriteFactory);
		DWriteResult = GlobalWriteFactory->CreateTextFormat(L"Consolas", 0, DWRITE_FONT_WEIGHT_REGULAR, DWRITE_FONT_STYLE_NORMAL, DWRITE_FONT_STRETCH_NORMAL, 36.0f, L"en-us", &GlobalTextFormat );
		GlobalTextFormat->SetWordWrapping(DWRITE_WORD_WRAPPING_NO_WRAP);
	}

	{
		WNDCLASS WindowClass = {};
		WindowClass.hInstance = Instance;
		WindowClass.lpfnWndProc = SysWindowProc;
		WindowClass.lpszClassName = L"zed";
		WindowClass.style = CS_OWNDC | CS_HREDRAW | CS_VREDRAW;
		ATOM WindowClassAtom = RegisterClass(&WindowClass);

		Invariant(WindowClassAtom);
	}

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
		// TODO: Lock to 60FPS.
		GlobalRenderTarget->BeginDraw();
		GlobalRenderTarget->Clear(D2D1::ColorF(D2D1::ColorF::White));
		Draw(&GapBuffer, 0, 0, 1920, 1080);
		//DrawCursor(GlobalZedBuffer);
		GlobalRenderTarget->EndDraw();
	}

	return 0;
}