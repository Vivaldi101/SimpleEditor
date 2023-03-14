
/////////////////////////
// TODO: Hone and refine the gap buffer invariants!!!!!!!
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

#define Implies(a, b) assert(!(a) || (b))
#define PreCondition(a) if(!(a)) __debugbreak();
#define PostCondition(a) if(!(a)) __debugbreak();
#define Invariant(a) if(!(a)) __debugbreak();

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


// ccggggccxxx

typedef s64 buffer_position;
struct zed_gap_buffer
{
	byte *Memory;
	buffer_position TotalSize;
	buffer_position CursorPosition; // Elements before the gap. First index into the gap.
	buffer_position CaretPosition; 
	buffer_position GapSizeLeft;
	buffer_position Count;
};
global zed_gap_buffer* GlobalZedBuffer;

function void
CursorInvariants(zed_gap_buffer *Buffer)
{
	Invariant(Buffer->CursorPosition >= 0);
	Invariant(Buffer->CursorPosition <= (Buffer->TotalSize - Buffer->GapSizeLeft));
	Invariant(Buffer->CursorPosition <= Buffer->Count);
}

function void
GapInvariants(zed_gap_buffer *Buffer)
{
	Invariant(Buffer->GapSizeLeft >= 0);
	Invariant(Buffer->GapSizeLeft == (Buffer->TotalSize - Buffer->Count));
}

function void
BufferInvariants(zed_gap_buffer *Buffer)
{
	Invariant(Buffer->Count <= Buffer->TotalSize);
	CursorInvariants(Buffer);
	GapInvariants(Buffer);
	Invariant(Buffer->CaretPosition == Buffer->CursorPosition); // Fix this.
}

function void
MoveRawMemory(byte *Destination, byte *Source, u64 Size)
{
	memmove(Destination, Source, Size);
}

function void
SetRawMemory(byte *Destination, int Value, u64 Size)
{
	memset(Destination, Value, Size);
}

function void
CopyRawMemory(byte *Destination, byte *Source, u64 Size)
{
	// TODO: Overlap conditions.
	memcpy(Destination, Source, Size);
}

function void 
Zed_InitializeGapBuffer(zed_gap_buffer *Buffer, size_t BufferSize, size_t GapSize)
{
	BufferInvariants(Buffer);
	ZeroStruct(Buffer);
	Buffer->Memory = Cast(HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, BufferSize), byte*);
	Invariant(GapSize <= BufferSize);
	Implies(BufferSize >= 0, Buffer->Memory);
	Implies(GapSize >= 0, Buffer->Memory);
	Buffer->TotalSize = BufferSize;
	Buffer->GapSizeLeft = GapSize;
	BufferInvariants(Buffer);
}

function void
Zed_ShiftToInsertPosition(zed_gap_buffer *Buffer, buffer_position At)
{
	BufferInvariants(Buffer);
	if (Buffer->CursorPosition > At)
	{
		// Shift count is from at to not including the cursor position (start of gap).
		size_t ShiftCount = Buffer->CursorPosition - At;
		MoveRawMemory(Buffer->Memory + At + Buffer->GapSizeLeft, Buffer->Memory + At, ShiftCount);
	}
	else if ((Buffer->CursorPosition + Buffer->GapSizeLeft-1) < At)
	{
		size_t ShiftCount = At - Buffer->CursorPosition;
		MoveRawMemory(Buffer->Memory + Buffer->CursorPosition, Buffer->Memory + At + Buffer->GapSizeLeft, ShiftCount);
	}
	else
	{
		Buffer->GapSizeLeft -= abs(At - Buffer->CursorPosition);
	}
	BufferInvariants(Buffer);
	Buffer->CursorPosition = At;
}

function void
Zed_InsertCharacter(zed_gap_buffer *Buffer, buffer_position At, char Char)
{
	BufferInvariants(Buffer);
	Zed_ShiftToInsertPosition(Buffer, At);

	// Needs to expand.
	if((Buffer->GapSizeLeft == 0))
	{
		buffer_position SizeAfterGap = Buffer->TotalSize - (Buffer->CursorPosition + Buffer->GapSizeLeft);
		Buffer->GapSizeLeft = Buffer->TotalSize;
		Buffer->TotalSize *= 2;
		Buffer->Memory = Cast(HeapReAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, Buffer->Memory, Buffer->TotalSize), byte*);

		// Move the elements after and including cursor to after the new gap.
		MoveRawMemory(Buffer->Memory + Buffer->CursorPosition + Buffer->GapSizeLeft, Buffer->Memory + Buffer->CursorPosition, SizeAfterGap);
	}
	Invariant(Buffer->CursorPosition == At);
	Buffer->Memory[Buffer->CursorPosition] = Char;
	Buffer->CursorPosition++;
	Buffer->GapSizeLeft--;
	Buffer->Count++;
	Buffer->CaretPosition = Buffer->CursorPosition;
	BufferInvariants(Buffer);
}

function void
Zed_AppendCharacter(zed_gap_buffer *Buffer, char Char)
{
	BufferInvariants(Buffer);
	// Needs to expand.
	if(Buffer->GapSizeLeft == 0)
	{
		buffer_position SizeAfterGap = Buffer->TotalSize - (Buffer->CursorPosition + Buffer->GapSizeLeft);
		Buffer->GapSizeLeft = Buffer->TotalSize;
		Buffer->TotalSize *= 2;
		Buffer->Memory = Cast(HeapReAlloc(GetProcessHeap(), 0, Buffer->Memory, Buffer->TotalSize), byte*);

		// Move the elements after and including cursor to after the new gap.
		MoveRawMemory(Buffer->Memory + Buffer->CursorPosition + Buffer->GapSizeLeft, Buffer->Memory + Buffer->CursorPosition, SizeAfterGap);
	}
	Buffer->Memory[Buffer->CursorPosition] = Char;
	Buffer->CursorPosition++;
	Buffer->GapSizeLeft--;
	Buffer->Count++;
	Buffer->CaretPosition = Buffer->CursorPosition;
	BufferInvariants(Buffer);
}


function void
Zed_MoveForwards(zed_gap_buffer *Buffer)
{
	BufferInvariants(Buffer);
	if (Buffer->CursorPosition < Buffer->Count)
	{
		Buffer->CaretPosition++;
		Buffer->CursorPosition++;
		MoveRawMemory(Buffer->Memory + Buffer->CursorPosition, Buffer->Memory + Buffer->CursorPosition + Buffer->GapSizeLeft, 1);
	}
	BufferInvariants(Buffer);
}

// c1gggg2cxxx
// cgggg12cxxx
function void
Zed_MoveBackwards(zed_gap_buffer *Buffer)
{
	BufferInvariants(Buffer);
	if (Buffer->CursorPosition > 0)
	{
		Buffer->CaretPosition--;
		Buffer->CursorPosition--;
		MoveRawMemory(Buffer->Memory + Buffer->CursorPosition + Buffer->GapSizeLeft, Buffer->Memory + Buffer->CursorPosition, 1);
	}
	BufferInvariants(Buffer);
}

function void
Zed_Backspace(zed_gap_buffer *Buffer)
{
	BufferInvariants(Buffer);
	if (Buffer->CursorPosition > 0)
	{
		Buffer->CursorPosition--;
		Buffer->CaretPosition--;
		Buffer->GapSizeLeft++;
		Buffer->Count--;
	}
	BufferInvariants(Buffer);
}

function b32
IsNewLine(byte C)
{
	b32 Result = (C == '\n\r' || C == '\r\n' || C == '\n');
	return Result;
}

function b32
IsNull(byte C)
{
	b32 Result = (C == 0);
	return Result;
}

function void
Zed_Delete(zed_gap_buffer *Buffer)
{
	BufferInvariants(Buffer);
	if (((Buffer->CursorPosition + Buffer->GapSizeLeft - 1) < (Buffer->TotalSize)))
	{
		BufferInvariants(Buffer);
		Buffer->GapSizeLeft++;
		Buffer->Count--;
		BufferInvariants(Buffer);
	}
	else if ((Buffer->CursorPosition + Buffer->GapSizeLeft - 1) == (Buffer->TotalSize-1))
	{
		Buffer->CaretPosition--;
	}
	BufferInvariants(Buffer);
}

function buffer_position
Zed_AdvanceBufferPosition(zed_gap_buffer *Buffer, buffer_position BufferPosition)
{
	BufferInvariants(Buffer);
	PreCondition(0 <= BufferPosition);
	PreCondition(BufferPosition < Buffer->TotalSize);
	if ((0 <= BufferPosition) && BufferPosition < (Buffer->CursorPosition - 1))
	{
		BufferPosition = BufferPosition + 1;
		PostCondition((0 < BufferPosition) && (BufferPosition < Buffer->CursorPosition));
	}
	else if (((Buffer->CursorPosition + Buffer->GapSizeLeft-1) <= BufferPosition) && ((BufferPosition+1) < Buffer->TotalSize))
	{
		BufferPosition = BufferPosition + 1;
		PostCondition(((Buffer->CursorPosition + Buffer->GapSizeLeft-1) < BufferPosition) && (BufferPosition < Buffer->TotalSize));
	}
	else if((BufferPosition+1) >= Buffer->CursorPosition)
	{
		BufferPosition += (Buffer->GapSizeLeft+1);
	}
	BufferInvariants(Buffer);
	return BufferPosition;
}

function buffer_position
Zed_CopyLineFromGapBuffer(char *Destination, size_t DestinationSize, zed_gap_buffer *Buffer, buffer_position BufferPosition)
{
	BufferInvariants(Buffer);
	buffer_position Result = BufferPosition;
	while (Buffer->Count > 0 && (BufferPosition < Buffer->TotalSize))
	{
		byte C = Buffer->Memory[BufferPosition];
		BufferPosition = Zed_AdvanceBufferPosition(Buffer, BufferPosition);
		*Destination++ = C;
	}

	Result = BufferPosition;
	BufferInvariants(Buffer);
	return Result;
}

// Fix the size of the cursor to match font size.
function void
Zed_DrawCaret(zed_gap_buffer *Buffer)
{
	D2D1_RECT_F Cursor;
	const int CaretWidth = 20.0f;
	const int CaretHeight = 40.0f;
	Cursor.left = (f32)Buffer->CaretPosition*CaretWidth;;
	Cursor.top = 0.0f;
	Cursor.right = Cursor.left + CaretWidth;;
	Cursor.bottom = CaretHeight;

	D2D1_COLOR_F OldColor = GlobalTextBrush->GetColor();
	D2D1_COLOR_F CursorColor = {1.0f, 0.0f, 0.0f, 1.0f};
	GlobalTextBrush->SetColor(&CursorColor);
	GlobalRenderTarget->DrawRectangle(Cursor, GlobalTextBrush, 2.0f);
	GlobalTextBrush->SetColor(&OldColor);
}

function void
Zed_DrawText(zed_gap_buffer *Buffer, f32 Left, f32 Top, f32 Width, f32 Height)
{
	byte Utf8[256];
	WCHAR Utf16[256];
	D2D1_RECT_F Layout;
	Layout.left = Left;
	Layout.top = Top;
	Layout.right = Layout.left + Width;
	Layout.bottom = Layout.top + Height;

	BufferInvariants(Buffer);
	buffer_position BufferPosition = Buffer->CursorPosition;
	// TODO: Fix this.
	//while (Buffer->Count > 1)
	{
		ZeroMemory(Utf8, sizeof(Utf8));
		CopyRawMemory((byte*)Utf8, Buffer->Memory, BufferPosition);
		//CopyRawMemory((byte*)Utf8 + BufferPosition, Buffer->Memory + BufferPosition + Buffer->GapSizeLeft, Buffer->Count - BufferPosition);
		
		//BufferPosition = Zed_CopyLineFromGapBuffer(Utf8, sizeof(Utf8) - 1, Buffer, BufferPosition);

		MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)Utf8, sizeof(Utf8), Utf16, sizeof(Utf16) / sizeof(*Utf16));
		GlobalRenderTarget->DrawText(Utf16, (UINT)wcslen(Utf16), GlobalTextFormat, Layout, GlobalTextBrush);

		//--Buffer->Count;
	}

	BufferInvariants(Buffer);
}

LRESULT CALLBACK
SysWindowProc(HWND Window, UINT Message, WPARAM WParam, LPARAM LParam)
{
	// TODO: Get the app data here with GetWindowLongPtrA()
	LRESULT Result = 0;
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
				if (VkCode == VK_BACK)
				{
					Zed_Backspace(GlobalZedBuffer);
				}
				else if (VkCode == 'x')
				{
					Zed_Delete(GlobalZedBuffer);
				}
				else if (VkCode == 'J')
				{
					Zed_MoveBackwards(GlobalZedBuffer);
				}
				else if (VkCode == 'K')
				{
					Zed_MoveForwards(GlobalZedBuffer);
				}
				else
				{
					// Cleanup
					{
						int BufferSize = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&WParam, 1, 0, 0, 0, 0);

						char* Buffer = (char*)_malloca(BufferSize);

						int Result = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&WParam, 1, Buffer, BufferSize, 0, 0);

						// Remove the <= 2 byte assumption.
						if (Result == 2)
						{
							Zed_InsertCharacter(GlobalZedBuffer, GlobalZedBuffer->CursorPosition, Buffer[0]);
							Zed_InsertCharacter(GlobalZedBuffer, GlobalZedBuffer->CursorPosition, Buffer[1]);
						}
						else if (Result == 1)
						{
							Zed_InsertCharacter(GlobalZedBuffer, GlobalZedBuffer->CursorPosition, Buffer[0]);
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

int WINAPI 
WinMain(HINSTANCE Instance, HINSTANCE, LPSTR, int)
{
	zed_gap_buffer Buffer = {};
	GlobalZedBuffer = &Buffer;
	u32 BufferSize = 1;
	Zed_InitializeGapBuffer(GlobalZedBuffer, BufferSize, BufferSize);
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
	RegisterClass(&WindowClass);

	// Adjust the client area related to the screen origin + client size.
	RECT DesiredWindow = { 500, 300, 800, 600 };
	AdjustWindowRect(&DesiredWindow, WS_OVERLAPPEDWINDOW, FALSE);
	HWND WindowHandle = CreateWindow(L"zed", L"zed", WS_OVERLAPPEDWINDOW | WS_VISIBLE, DesiredWindow.left, DesiredWindow.top, DesiredWindow.right, DesiredWindow.bottom, 0, 0, Instance, 0);
	UpdateWindow(WindowHandle);

	while (!GlobalQuit)
	{
		MSG Message;
		while (PeekMessage(&Message, 0, 0, 0, PM_REMOVE))
		{
			TranslateMessage(&Message);
			DispatchMessage(&Message);
		}
#if 1
		// TODO: Cap to 60FPS.
		// TODO: Figure out why cursor is drawn weirdly.
		GlobalRenderTarget->BeginDraw();
		GlobalRenderTarget->Clear(D2D1::ColorF(D2D1::ColorF::White));
		Zed_DrawText(GlobalZedBuffer, 0, 0, 800, 600);
		Zed_DrawCaret(GlobalZedBuffer);
		GlobalRenderTarget->EndDraw();
#endif
	}

	return 0;
}