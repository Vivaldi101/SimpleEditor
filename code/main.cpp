
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

#define global static
#define local static
#define function static
#define forceinline __forceinline

#define Cast(x, t) (t)(x)
#define ZeroStruct(x) memset((x), 0, sizeof(*(x)));
#define ArrayCount(a) sizeof((a)) / sizeof((*a))
#define Halt __debugbreak();

#ifdef _DEBUG

#define Pre(a) if(!(a)) Halt
#define Post(a) if(!(a)) Halt
#define Invariant(a) if(!(a)) Halt
#define Implies(a, b) (!(a) || (b))

#define ForI(b, n) for(u32 i = (b); i < (n); ++i)
#define ForJ(b, n) for(u32 j = (b); j < (n); ++j)
#define ForK(b, n) for(u32 k = (b); k < (n); ++k)

#define EQ(n, p) [&]() -> bool {for(size_t i__ = 0u; i__ < (n); ++i__) { if ((p)) { return true; } } return false; }()
#define UQ(n, p) [&]() -> bool {for(size_t i__ = 0u; i__ < (n); ++i__) { if (!(p)) { return false; } } return true; }()

#else

#define Pre(a)
#define Post(a)
#define Invariant(a)
#define Implies(a, b)

#define EQ(a, n, p) 
#define UQ(a, n, p)

#define ForI(n) 
#define ForJ(n) 
#define ForK(n) 

#endif

global bool GlobalQuit;

/////////////////////////
// TODO: Remove the globals.
/////////////////////////

global ID2D1Factory *GlobalD2D1Factory;
global IDWriteFactory *GlobalWriteFactory;
global ID2D1HwndRenderTarget *GlobalRenderTarget;
global IDWriteTextFormat *GlobalTextFormat;
global ID2D1SolidColorBrush* GlobalTextBrush;

global unsigned int GlobalPaneX;
global unsigned int GlobalPaneY;

typedef u64 buffer_position;
typedef u64 cursor_position;

struct gap_buffer
{
	buffer_position GapBegin;
	buffer_position GapEnd;	// [GapBegin, GapEnd)
	buffer_position End;	
	cursor_position Cursor; // [Cursor, End)
	byte *Memory;

	//byte Reserved[24];	// Align to 64 byte cache line. TODO: Change this to match.
};

struct pane
{
	cursor_position Start; // [Start, End)
	cursor_position End;
};

global pane GlobalCurrentPane;

// Post and precondition for gap size staying same.

#define GapSize(Buffer) ((Buffer)->GapEnd - (Buffer)->GapBegin)
#define IsGapFull(Buffer) (GapSize((Buffer)) == 1)
#define BufferSize(Buffer) ((Buffer)->End - GapSize(Buffer))
#define IsCursorInGapExcl(Buffer) ((Buffer)->GapBegin < (Buffer)->Cursor && (Buffer)->Cursor < (Buffer)->GapEnd)
#define IsIndexInGapExcl(Buffer, Index) ((Buffer)->GapBegin < (Index) && (Index) < (Buffer)->GapEnd)

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

forceinline void
GapBufferInvariants(gap_buffer *Buffer)
{
	Invariant(Buffer->Cursor < Buffer->End);
	Invariant(Buffer->Cursor <= BufferSize(Buffer));

	Invariant(!IsCursorInGapExcl(Buffer));

	Invariant(Buffer->GapBegin < Buffer->GapEnd);
	Invariant(Buffer->GapEnd <= Buffer->End);
}
#else
function void
DebugMessage(const char* format, ...) { }

function void
GapBufferInvariants(gap_buffer *Buffer) { }
#endif

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

	HeapFree(GetProcessHeap(), HEAP_ZERO_MEMORY, Buffer->Memory);
}

function void 
Initialize(gap_buffer *Buffer, size_t Size)
{
	Pre(Buffer);
	Pre(Size > 1);

	// Initialize the invariants.
	Buffer->GapBegin = 0;
	Buffer->Cursor = Buffer->GapBegin;
	Buffer->Memory = Cast(HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, Size), byte*);
	Buffer->End = Size;
	Buffer->GapEnd = Buffer->End;

	Post(!IsGapFull(Buffer));

	// wp(S, GapEnd - GapBegin != 1)
	// wp(S, End - GapBegin != 1)
	// wp(S, Size - GapBegin != 1)
	// wp(S, Size - 0 != 1)
	// (Size - 0 != 1)
	// Size != 1

	Post(Buffer->Memory);

	Post(GapSize(Buffer) == Size);
	Post(BufferSize(Buffer) == 0);

	Post(((2 * BufferSize(Buffer)) - Buffer->GapBegin) != 1);

	// wp(Buffer->Cursor < Buffer->End);
	// wp(Buffer->Cursor < Size);
	// wp(0 < Size);
	// (0 < Size);
	// (0 < Size) && (Size != 1);
	// => Size > 1

	GapBufferInvariants(Buffer);
}

forceinline char
GetCharAtIndex(gap_buffer* Buffer, cursor_position CursorIndex)
{
	Pre(Buffer);
	Pre(CursorIndex < Buffer->End - GapSize(Buffer));

	GapBufferInvariants(Buffer);

	buffer_position BufferIndex = CursorIndex < Buffer->GapBegin ? CursorIndex : CursorIndex + GapSize(Buffer);

	Post(BufferIndex < Buffer->End);

	// wp(Index < Buffer->End)
	// wp(Cursor < Buffer->End)
	// (Cursor < Buffer->End)

	// wp(Index < Buffer->End)
	// wp(Cursor + GapSize < Buffer->End)
	// wp(Cursor < Buffer->End - GapSize)

	GapBufferInvariants(Buffer);

	return Buffer->Memory[BufferIndex];
}

forceinline char
GetCharAtCursor(gap_buffer *Buffer)
{
	Pre(Buffer);
	Pre(Buffer->Cursor < Buffer->End - GapSize(Buffer));

	GapBufferInvariants(Buffer);

	buffer_position Index = Buffer->Cursor < Buffer->GapBegin ? Buffer->Cursor : Buffer->Cursor + GapSize(Buffer);

	Post(Index < Buffer->End);

	// wp(Index < Buffer->End)
	// wp(Cursor < Buffer->End)
	// (Cursor < Buffer->End)

	// wp(Index < Buffer->End)
	// wp(Cursor + GapSize < Buffer->End)
	// wp(Cursor < Buffer->End - GapSize)

	GapBufferInvariants(Buffer);

	return Buffer->Memory[Index];
}

function void
MoveForwards(gap_buffer *Buffer)
{
	Pre(Buffer);
	Pre(Buffer->Cursor < BufferSize(Buffer));

	GapBufferInvariants(Buffer);

	const buffer_position OldBufferSize = BufferSize(Buffer);

	MoveBytes(Buffer->Memory + Buffer->GapBegin, Buffer->Memory + Buffer->GapEnd, 1);

	Buffer->Cursor++;

	Buffer->GapBegin++;
	Buffer->GapEnd++;

	//Buffer->Memory[Buffer->GapEnd - 1] = 0;

	Post(OldBufferSize == BufferSize(Buffer));

	GapBufferInvariants(Buffer);
}

function void
MoveBackwards(gap_buffer *Buffer)
{
	Pre(Buffer);
	Pre(Buffer->Cursor != 0);

	GapBufferInvariants(Buffer);

	const buffer_position OldBufferSize = BufferSize(Buffer);

	MoveBytes(Buffer->Memory + Buffer->GapEnd - 1, Buffer->Memory + Buffer->GapBegin - 1, 1);
	Buffer->Cursor--;

	Buffer->GapEnd--;
	Buffer->GapBegin--;

	//Buffer->Memory[Buffer->GapBegin] = 0;

	Post(OldBufferSize == BufferSize(Buffer));

	GapBufferInvariants(Buffer);
}

function void
SetCursorToBeginOfLine(gap_buffer* Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	do
	{
		if (Buffer->Cursor == 0)
		{
			return;
		}
		MoveBackwards(Buffer);
		if (Buffer->Cursor >= Buffer->End - GapSize(Buffer))
		{
			return;
		}
	} while (GetCharAtCursor(Buffer) != '\n');

	Post(GetCharAtCursor(Buffer) == '\n' || Buffer->Cursor == 0);

	if (GetCharAtCursor(Buffer) == '\n')
	{
		MoveForwards(Buffer);
	}

	GapBufferInvariants(Buffer);
}

// TODO: FIX
function void
SetEndOfLineCursor(gap_buffer* Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	while(Buffer->Cursor < BufferSize(Buffer))
	{
		if (Buffer->Memory[Buffer->Cursor] == '\n')
		{
			MoveBackwards(Buffer);
			break;
		}

		MoveForwards(Buffer);
	}

	Post((Implies(Buffer->Cursor < BufferSize(Buffer), Buffer->Memory[Buffer->Cursor+1] == '\n')));

	GapBufferInvariants(Buffer);
}

function bool
TryInsertCharacter(gap_buffer *Buffer, char Char)
{
	Pre(Buffer);
	Pre(Buffer->End * 2 > 1 + Buffer->GapBegin);

	GapBufferInvariants(Buffer);

	if(IsGapFull(Buffer))
	{
		const buffer_position OldEnd = Buffer->End;
		const buffer_position OldGapEnd = Buffer->GapEnd;
		const buffer_position OldGapBegin = Buffer->GapBegin;
		const buffer_position BufferRemnants = OldEnd - OldGapEnd;

		const buffer_position NewBufferSize = OldEnd * 2 + BufferRemnants;

		const void* RealloctedMemory = Cast(HeapReAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, Buffer->Memory, NewBufferSize), byte*);

		if (!RealloctedMemory)
		{
			DeInitialize(Buffer);

			return false;
		}

		Buffer->Memory = (byte*)RealloctedMemory;

		Buffer->End = NewBufferSize;
		Buffer->GapEnd = Buffer->End - BufferRemnants;

		// Shuffle the characters after the previous gap after new gap end.
		MoveBytes(Buffer->Memory + Buffer->GapEnd, Buffer->Memory + OldGapEnd, BufferRemnants);

		// New gap not full anymore.
		// wp(S, GapSize((Buffer)) != 1)
		// wp(S, (GapEnd - GapBegin) != 1)

		// wp(S, (NewBufferSize - BufferRemnants - GapBegin) != 1)
		// wp(S, (OldEnd * 2 + BufferRemnants - BufferRemnants - GapBegin) != 1)
		// wp(S, (OldEnd * 2 + OldEnd - OldGapEnd - (OldEnd - OldGapEnd) - GapBegin) != 1)
		// wp(S, (OldEnd * 2 + OldEnd - OldGapEnd - OldEnd + OldGapEnd - GapBegin) != 1)

		// wp(S, (OldEnd * 2 - GapBegin) != 1)
		// wp(S, OldEnd * 2 - GapBegin != 1)
		// wp(S, OldEnd * 2 != 1 + GapBegin)	== precond

		// wp(S, OldEnd * 2 != 1 + GapBegin)   == precond

		// wp(S, GapEnd != 1 + GapBegin) == IsGapFull

		// wp(S, GapEnd != OldEnd * 2) == ?

		Post(!IsGapFull(Buffer));

		// Make sure old buffer remnants fit after the gap.
		// wp(S, Buffer->GapEnd == Buffer->End - BufferRemnants)
		// wp(S, NewBufferSize - BufferRemnants == NewBufferSize - BufferRemnants)
		// wp(S, T)
		// T
		Post(Buffer->GapEnd == Buffer->End - BufferRemnants);

		// Final new buffer size.
		Post(NewBufferSize == OldEnd * 2 + BufferRemnants);
	}

	Buffer->Memory[Buffer->GapBegin] = Char;
	Buffer->Cursor++;

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
MoveUp(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	buffer_position ColumnCursorIndex = Buffer->Cursor;

	SetCursorToBeginOfLine(Buffer);

	ColumnCursorIndex = ColumnCursorIndex - Buffer->Cursor;

	MoveBackwards(Buffer);

	SetCursorToBeginOfLine(Buffer);

	while (ColumnCursorIndex > 0)
	{
		MoveForwards(Buffer);
		--ColumnCursorIndex;
	}

	//DebugMessage("Column cursor: \t\t%d\n", ColumnCursor);

	GapBufferInvariants(Buffer);
}

function void
MoveDown(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	buffer_position GapEnd = Buffer->GapEnd + 1;
	buffer_position GapShift = 0;

	GapBufferInvariants(Buffer);
}

// Fix similarly to moving backwards.
function void
Backspace(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);
	const buffer_position OldBufferSize = BufferSize(Buffer);

	// Cant backspace anymore.
	if (Buffer->Cursor == 0)
	{
		return;
	}

	Buffer->Cursor--;

	Buffer->GapBegin--;

	Buffer->Memory[Buffer->GapBegin] = 0;

	Post(OldBufferSize - 1 == BufferSize(Buffer));

	GapBufferInvariants(Buffer);
}

function void
DrawCursor(f32 CursorLeft, f32 CursorTop, f32 CursorRight, f32 CursorBottom, D2D1_COLOR_F CursorColor)
{
	D2D1_ROUNDED_RECT CursorRounded;
	D2D1_RECT_F Cursor;

	Cursor.left = CursorLeft;
	Cursor.top = CursorTop;
	Cursor.right = CursorRight;
	Cursor.bottom = CursorBottom;

	CursorRounded.rect = Cursor;
	CursorRounded.radiusX = 5.0f;
	CursorRounded.radiusY = 5.0f;

	D2D1_COLOR_F OldColor = GlobalTextBrush->GetColor();
	GlobalTextBrush->SetColor(&CursorColor);
	GlobalRenderTarget->DrawRoundedRectangle(CursorRounded, GlobalTextBrush, 2.0f, NULL);
	GlobalTextBrush->SetColor(&OldColor);
}

function void
Draw(gap_buffer *Buffer, pane *Pane, f32 Left, f32 Top, f32 Width, f32 Height)
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

	// TODO: Handle multibyte unicode advancements.

	buffer_position UtfIndex = 0;
	const cursor_position PaneEnd = Pane->End;
	for (cursor_position PaneCursor = Pane->Start; PaneCursor != PaneEnd; PaneCursor++)
	{
		GapBufferInvariants(Buffer);

		if (PaneCursor < Buffer->End - GapSize(Buffer))
		{
			Utf8[UtfIndex] = GetCharAtIndex(Buffer, PaneCursor);
			MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)Utf8 + UtfIndex, 1, Utf16 + UtfIndex, sizeof(Utf16));
			UtfIndex++;
		}
		Invariant(UtfIndex <= ArrayCount(Utf8) && UtfIndex <= ArrayCount(Utf16));
		GapBufferInvariants(Buffer);
	}

	Pre(ArrayCount(Utf16) > 0);
	Utf16[ArrayCount(Utf16) - 1] = 0;

	GlobalRenderTarget->PushAxisAlignedClip(&Layout, D2D1_ANTIALIAS_MODE_ALIASED);

	IDWriteTextLayout* TextLayout;
	GlobalWriteFactory->CreateTextLayout(Utf16, (UINT)wcslen(Utf16), GlobalTextFormat, Layout.right - Layout.left, Layout.bottom - Layout.top, &TextLayout);

	Pre(TextLayout);
	GlobalRenderTarget->DrawTextLayout(D2D1::Point2F(Layout.left, Layout.top), TextLayout, GlobalTextBrush);

	f32 CursorX, CursorY;
	DWRITE_HIT_TEST_METRICS CursorMetrics;
	TextLayout->HitTestTextPosition((u32)Buffer->Cursor, FALSE, &CursorX, &CursorY, &CursorMetrics);

	Pre(TextLayout);

	TextLayout->Release();

	f32 CursorLeft = CursorX + Layout.left;
	f32 CursorTop = CursorY + Layout.top;
	f32 CursorRight = CursorLeft + CursorMetrics.width;
	f32 CursorBottom = CursorTop + CursorMetrics.height;

	const D2D1_COLOR_F CursorColor = {1.0f, 1.0f, 0.0f, 1.0f};

	DrawCursor(CursorLeft, CursorTop, CursorRight, CursorBottom, CursorColor);

	if (Buffer->Cursor < Buffer->End - GapSize(Buffer))
	{
		const char CursorChar = GetCharAtCursor(Buffer);
		DebugMessage("Cursor char: %c\n", CursorChar);
	}

	GlobalRenderTarget->PopAxisAlignedClip();

	GapBufferInvariants(Buffer);
}

function void
UpdateScrollView(gap_buffer *Buffer)
{
	Pre(Buffer);
}

function void
ScrollPaneDown(gap_buffer *Buffer)
{
	Pre(Buffer);
	GapBufferInvariants(Buffer);

	SetCursorToBeginOfLine(Buffer);

	//GlobalCurrentPane.Start += 20;
	//GlobalCurrentPane.End += 20;
}

function void
LoadTestFile(gap_buffer *Buffer)
{
	Pre(Buffer);
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
					else if (VkCode == '0')
					{
						SetCursorToBeginOfLine(Buffer);
					}
					else if (VkCode == '$')
					{
						SetEndOfLineCursor(Buffer);
					}
					else
					{
						// Cleanup
						{
							const int BufferSize = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&WParam, 1, 0, 0, 0, 0);

							char* MultiBytes = (char*)_malloca(BufferSize);

							if (!MultiBytes)
							{
								Halt;
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
		case WM_KEYDOWN:
			{
				switch(WParam)
				{
				case VK_LEFT:	
					if (Buffer->Cursor != 0)
					{
						MoveBackwards(Buffer);
					}
					break;
				case VK_RIGHT:	
					if (Buffer->Cursor < BufferSize(Buffer))
					{
						MoveForwards(Buffer);
					}
					break; 
				case VK_UP:	
					//MoveUp(Buffer); 
					break; 
				case VK_DOWN:	
					//MoveDown(Buffer); 
					ScrollPaneDown(Buffer);
					break; 
				case VK_END:	
					LoadTestFile(Buffer); 
					break;
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

u32 FindLastMatch(gap_buffer* Buffer, u32 i, u32 n)
{
	u32 k = n-1;
	while (Buffer->Memory[k] != Buffer->Memory[i])
	{
		k--;
		Invariant(Implies(0 < k && k < i, Buffer->Memory[k+1] != Buffer->Memory[i]));
	}

	Post(Buffer->Memory[i] == Buffer->Memory[k]);

	return k;
}

u32 FindFirstMatch(gap_buffer* Buffer, u32 i)
{
	u32 k = 0;
	while (Buffer->Memory[k] != Buffer->Memory[i])
	{
		k++;
		Invariant(Implies(0 < k && k < i, Buffer->Memory[k-1] != Buffer->Memory[i]));
	}

	Post(Buffer->Memory[i] == Buffer->Memory[k]);

	return k;
}

int WINAPI 
WinMain(HINSTANCE Instance, HINSTANCE, LPSTR, int)
{
	gap_buffer GapBuffer = {};

	GlobalCurrentPane.Start = 0;
	GlobalCurrentPane.End = 512;

	// TODO: Reasonable intial buffer size
	Initialize(&GapBuffer, 2);

	// COM stuff.
	{
		HRESULT DWriteResult = D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED, &GlobalD2D1Factory);
		DWriteResult = DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED, __uuidof(IDWriteFactory), (IUnknown**)&GlobalWriteFactory);
		DWriteResult = GlobalWriteFactory->CreateTextFormat(L"Consolas", 0, DWRITE_FONT_WEIGHT_SEMI_BOLD, DWRITE_FONT_STYLE_NORMAL, DWRITE_FONT_STRETCH_NORMAL, 32.0f, L"en-us", &GlobalTextFormat);
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
	int X = 500;
	int Y = 300;
	int Width = 800;
	int Height = 600;
	RECT DesiredWindow = { X, Y, Width, Height };
	AdjustWindowRect(&DesiredWindow, WS_OVERLAPPEDWINDOW, FALSE);
	HWND WindowHandle = CreateWindow(L"zed", L"Editor", WS_OVERLAPPEDWINDOW, DesiredWindow.left, DesiredWindow.top, DesiredWindow.right, DesiredWindow.bottom, 0, 0, Instance, 0);

	Invariant(WindowHandle);

	// TODO: Attach pane or do a pointer to the current buffer inside the pane structure.
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
		GlobalRenderTarget->Clear(D2D1::ColorF(D2D1::ColorF::LightBlue));
		Draw(&GapBuffer, &GlobalCurrentPane, 0, 0, (f32)Width, (f32)Height);
		GlobalRenderTarget->EndDraw();
	}

	DeInitialize(&GapBuffer);

	return 0;
}