
/////////////////////////
// TODO: Hone and refine the gap buffer invariants!!!!!!!
// TODO: Remove the globals.
// TODO: One megastruct.
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

#define Pre(a) if(!(a)) __debugbreak();
#define Post(a) if(!(a)) __debugbreak();
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

// Post and precondition for gap size staying same.

#define GapSize(Buffer) ((Buffer)->GapEnd - (Buffer)->GapBegin)
#define IsGapFull(Buffer) GapSize((Buffer)) == 0
#define BufferSize(Buffer) (Buffer)->End - GapSize(Buffer)
#define IsCursorInGap(Buffer) ((Buffer)->GapBegin <= (Buffer)->Cursor && (Buffer)->Cursor <= (Buffer)->GapEnd)

function void
GapBufferInvariants(gap_buffer *Buffer)
{
	Invariant(Buffer->Cursor >= 0);
	Invariant(Buffer->GapBegin >= 0);

	Invariant(Buffer->GapBegin <= Buffer->GapEnd);

	Invariant(Buffer->GapEnd <= Buffer->End);
	Invariant(Buffer->Cursor <= Buffer->End);
}

function bool
IsAscii(char C)
{
	return isascii(C);
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

function void
InsertCharacter(gap_buffer *Buffer, char Char)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	// Needs to expand the gap for the new reallocated buffer.
	if(IsGapFull(Buffer))
	{
		Pre(Buffer->GapBegin == Buffer->GapEnd);

		const buffer_position NewBufferSize = (Buffer->End + 1) * 2;
		const buffer_position NewGapSize = NewBufferSize / 2;
		const buffer_position OldGapEnd = Buffer->GapEnd;
		const buffer_position OldGapBegin = Buffer->GapBegin;
		const buffer_position End = Buffer->End;

		Buffer->Memory = Cast(HeapReAlloc(GetProcessHeap(), 0, Buffer->Memory, NewBufferSize), byte*);
		Buffer->End = NewBufferSize - 1;
		Buffer->GapEnd += NewGapSize;

		MoveBytes(Buffer->Memory + Buffer->GapEnd, Buffer->Memory + OldGapEnd, BufferSize(Buffer) - OldGapBegin);

		Post(NewBufferSize == (NewGapSize * 2));
		Post(Buffer->GapBegin != Buffer->GapEnd);
	}

	Buffer->Memory[Buffer->GapBegin] = Char;
	Buffer->GapBegin++;

	Buffer->Cursor++;

	GapBufferInvariants(Buffer);
}

function void
InsertNewline(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	InsertCharacter(Buffer, '\n');
	Buffer->Cursor = 0;		// Reset the cursor to the beginning.

	GapBufferInvariants(Buffer);
}

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

	const buffer_position OldCursor = Buffer->Cursor;

	if (Buffer->Cursor != 0) // Remain on this line.
	{
		Buffer->Cursor--;

		Post(Buffer->Cursor >= 0);
		Post(Buffer->Cursor < OldCursor);
	}
	else if (Buffer->Cursor == 0) // Move up a line.
	{
		//Buffer->Cursor = Buffer->GapBegin - 1;

		Post(Buffer->Cursor == OldCursor);	// Empty previous line.
	}

	Buffer->GapBegin--;

	GapBufferInvariants(Buffer);
}

function void
MoveForwards(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	const buffer_position OldGapSize = GapSize(Buffer);

	if (Buffer->GapEnd == Buffer->End)
	{
		return;
	}

	MoveBytes(Buffer->Memory + Buffer->GapBegin, Buffer->Memory + Buffer->GapEnd + 1, 1);
	Buffer->GapBegin++;
	Buffer->GapEnd++;
	Buffer->Cursor++;

	Post(OldGapSize == GapSize(Buffer));

	GapBufferInvariants(Buffer);
}

function void
MoveBackwards(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);
	const buffer_position OldGapSize = GapSize(Buffer);

	if (Buffer->GapBegin == 0 || Buffer->Cursor == 0)
	{
		return;
	}

	MoveBytes(Buffer->Memory + Buffer->GapEnd, Buffer->Memory + Buffer->GapBegin - 1, 1);
	Buffer->GapBegin--;
	Buffer->GapEnd--;
	Buffer->Cursor--;

	GapBufferInvariants(Buffer);
}

// Fix the size of the cursor to match font size.
// Fix the line alignment.
function void
DrawCursor(buffer_position CursorLeft, buffer_position CursorTop)
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
	buffer_position GapEnd = Buffer->GapEnd;
	buffer_position End = Buffer->End;
	buffer_position Cursor = Buffer->Cursor;
	buffer_position Line = 0;
	buffer_position UtfIndex = 0;

	// TODO: Handle multibyte unicode advancements and new lines.
	// TODO: Optimize.
	for (buffer_position i = 0; i < GapBegin; ++i)
	{
		if (!IsAscii(Buffer->Memory[i]))
		{
			continue;
		}
		CopyBytes(Utf8 + UtfIndex, Buffer->Memory + i, 1);
		MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)Utf8 + UtfIndex, 1, Utf16 + UtfIndex, sizeof(Utf16));
		UtfIndex++;
		//Cursor++;
		if (Utf8[i] == '\n')
		{
			Line++;
		}
	}

	for (buffer_position i = GapEnd + 1; i <= End; ++i)
	{
		if (!IsAscii(Buffer->Memory[i]))
		{
			continue;
		}
		CopyBytes(Utf8 + UtfIndex, Buffer->Memory + i, 1);
		MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)Utf8 + UtfIndex, 1, Utf16 + UtfIndex, sizeof(Utf16));
		UtfIndex++;
		//Cursor++;
		if (Utf8[i] == '\n')
		{
			Line++;
		}
	}

	DrawCursor(Cursor, Line);

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
						InsertNewline(GapBuffer);
					}
					else if (VkCode == VK_BACK)
					{
						Backspace(GapBuffer);
					}
					else if (VkCode == 'x')
					{
						//Delete(GlobalZedBuffer);
					}
					else if (VkCode == 'J')
					{
						MoveBackwards(GapBuffer);
					}
					else if (VkCode == 'K')
					{
						MoveForwards(GapBuffer);
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
	Initialize(&GapBuffer, 4);

	// Stupid dwrite COM shit.
	{
		HRESULT DWriteResult = D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED, &GlobalD2D1Factory);
		DWriteResult = DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED, __uuidof(IDWriteFactory), (IUnknown**)&GlobalWriteFactory);
		DWriteResult = GlobalWriteFactory->CreateTextFormat(L"Consolas", 0, DWRITE_FONT_WEIGHT_REGULAR, DWRITE_FONT_STYLE_NORMAL, DWRITE_FONT_STRETCH_NORMAL, 36.0f, L"en-us", &GlobalTextFormat );
		GlobalTextFormat->SetWordWrapping(DWRITE_WORD_WRAPPING_NO_WRAP);
	}

	WNDCLASS WindowClass = {};
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
		// TODO: Lock to 60FPS.
		GlobalRenderTarget->BeginDraw();
		GlobalRenderTarget->Clear(D2D1::ColorF(D2D1::ColorF::White));
		Draw(&GapBuffer, 0, 0, 800, 600);
		//DrawCursor(GlobalZedBuffer);
		GlobalRenderTarget->EndDraw();
	}

	return 0;
}