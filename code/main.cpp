
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <windows.h>
#include <d2d1.h>
#include <dwrite.h>
#include <malloc.h>
#include <memory>

#include "utils.h"

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

typedef size_t usize;

typedef u32 b32;
typedef float f32;
typedef double f64;

struct uint2
{
   u32 x, y;
};

#define global static
#define local static
#define function static

#define forceinline 

#define cast(x, t) (t)(x)
#define zero_struct(x) memset((x), 0, sizeof(*(x)));
#define array_count(a) sizeof((a)) / sizeof((*a))
#define halt __debugbreak();

#ifdef _DEBUG

#define pre(a) if(!(a)) halt
#define post(a) if(!(a)) halt
#define invariant(a) if(!(a)) halt
#define implies(a, b) (!(a) || (b))
#define iff(a, b) ((a) == (b))

#define for_i(b, n) for(u32 i = (b); i < (n); ++i)
#define for_j(b, n) for(u32 j = (b); j < (n); ++j)
#define for_k(b, n) for(u32 k = (b); k < (n); ++k)

#define EQ(n, p) [&]() -> bool {for(usize i__ = 0u; i__ < (n); ++i__) { if ((p)) { return true; } } return false; }()
#define UQ(n, p) [&]() -> bool {for(usize i__ = 0u; i__ < (n); ++i__) { if (!(p)) { return false; } } return true; }()
#define CQ(n, p) [&]() -> usize {usize counter = 0; for(usize i__ = 0u; i__ < (n); ++i__) { if ((p)) { ++counter; } } return counter; }()

#else

#define pre(a)
#define post(a)
#define invariant(a)
#define implies(a, b)
#define iff(a, b)

#define EQ(a, n, p) 
#define UQ(a, n, p)
#define CQ(n, p)

#define for_i(n) 
#define for_j(n) 
#define for_k(n) 

#endif

global bool global_quit;

global ID2D1Factory* GlobalD2D1Factory;
global IDWriteFactory* global_write_factory;
global ID2D1HwndRenderTarget* global_render_target;
global IDWriteTextFormat* global_text_format;
global ID2D1SolidColorBrush* global_text_brush;
global IDWriteTextLayout* global_text_layout;

typedef u64 buffer_position;	// non-logical position
typedef u64 cursor_position;	// logical position

__declspec(align(64))	// align to cache line.
struct gap_buffer
{
   buffer_position gap_begin;
   buffer_position gap_end;	// [gap_begin, gap_end) - half-open interval
   buffer_position end;
   cursor_position cursor; // [cursor, end). logical cursor position.
   u32 ws_count;			// TODO: put this into cold data
   u32 word_count;			// TODO: put this into cold data
   f64 time_since_last_insert[256];
   byte* memory;
};

struct pane
{
   cursor_position begin; // [Begin, end) - half-open interval
   cursor_position end;
};

global pane global_current_pane;

// post and precondition for gap size staying same.

#define gap_size(buffer) ((buffer)->gap_end - (buffer)->gap_begin)
#define scroll_size(scroll) ((scroll)->end - (scroll)->begin)

#define is_gap_full(buffer) (gap_size((buffer)) == 1)
#define buffer_size(buffer) ((buffer)->end - gap_size(buffer))
//#define is_cursor_in_gap_excl(buffer) ((buffer)->gap_begin < (buffer)->cursor && (buffer)->cursor < (buffer)->gap_end)
//#define is_index_in_gap_excl(buffer, index) ((buffer)->gap_begin < (index) && (index) < (buffer)->gap_end)

#ifdef _DEBUG
function void
debug_message(const char* format, ...)
{
   char temp[1024];
   va_list args;
   va_start(args, format);
   //vswprintf(temp, format, args);
   va_end(args);
   OutputDebugStringA(temp);
}

function void
gap_buffer_invariants(gap_buffer* buffer)
{
   // buffer index invariant
   invariant(buffer->cursor < buffer->end);

   // logical index invariant
   invariant(buffer->cursor <= buffer_size(buffer));

   // gap-buffer index invariant
   invariant(buffer->gap_begin < buffer->gap_end);
   invariant(buffer->gap_end <= buffer->end);
}

function void
scroll_pane_invariants(pane* scroll, gap_buffer* buffer)
{
   invariant(scroll->begin < scroll->end);

   // TODO: should probably be scroll->end < buffer_size(buffer)
   invariant(scroll->end <= buffer->end);
}

#else
function void
debug_message(const char* format, ...) {}

function void
gap_buffer_invariants(gap_buffer* buffer) {}

function void
scroll_pane_invariants(pane* scroll, gap_buffer* buffer) {}
#endif

// TODO: same case as the rest
static s64 global_game_time_residual;
static s64 global_perf_counter_frequency;

static s64 clock_query_counter()
{
   LARGE_INTEGER result;
   QueryPerformanceCounter(&result);

   return result.QuadPart;
}

static LARGE_INTEGER clock_query_frequency()
{
   LARGE_INTEGER result;
   QueryPerformanceFrequency(&result);

   global_perf_counter_frequency = result.QuadPart;

   return result;
}

static f64 clock_seconds_elapsed(s64 start, s64 end)
{
   assert(global_perf_counter_frequency);

   return ((f64)end - (f64)start) / (f64)global_perf_counter_frequency;
}

static f64 clock_time_to_counter(f64 time)
{
   return (f64)global_perf_counter_frequency * time;
}

static void frame_sync(f64 frame_delta)
{
   int num_frames_to_run = 0;
   const s64 counter_delta = (s64)(clock_time_to_counter(frame_delta) + .5f);

   for (;;)
   {
      const s64 current_counter = clock_query_counter();
      static s64 last_counter = 0;
      if (last_counter == 0)
         last_counter = current_counter;

      s64 delta_counter = current_counter - last_counter;
      last_counter = current_counter;

      global_game_time_residual += delta_counter;

      for (;;)
      {
         // how much to wait before running the next frame
         if (global_game_time_residual < counter_delta)
            break;
         global_game_time_residual -= counter_delta;
         num_frames_to_run++;
      }
      if (num_frames_to_run > 0)
         break;

      Sleep(0);
   }
}

function void
move_bytes(byte* destination, byte* source, u64 size)
{
   MoveMemory(destination, source, size);
}

function void
set_bytes(byte* destination, int value, u64 size)
{
   FillMemory(destination, size, value);
}

function void
copy_bytes(byte* destination, byte* source, u64 size)
{
   CopyMemory(destination, source, size);
}

function void
de_initialize(gap_buffer* buffer)
{
   gap_buffer_invariants(buffer);
   pre(buffer);

   HeapFree(GetProcessHeap(), HEAP_ZERO_MEMORY, buffer->memory);
}

function void
initialize(gap_buffer* buffer, usize size)
{
   pre(buffer);
   pre(size > 1);

   // initialize the invariants.
   buffer->gap_begin = 0;
   buffer->cursor = buffer->gap_begin;
   buffer->memory = cast(HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, size), byte*);
   buffer->end = size;
   buffer->gap_end = buffer->end;

   post(!is_gap_full(buffer));

   // wp(S, gap_end - gap_begin != 1)
   // wp(S, end - gap_begin != 1)
   // wp(S, size - gap_begin != 1)
   // wp(S, size - 0 != 1)
   // (size - 0 != 1)
   // size != 1

   post(buffer->memory);

   post(gap_size(buffer) == size);
   post(buffer_size(buffer) == 0);

   post(((2 * buffer_size(buffer)) - buffer->gap_begin) != 1);

   // wp(buffer->cursor < buffer->end);
   // wp(buffer->cursor < size);
   // wp(0 < size);
   // (0 < size);
   // (0 < size) && (size != 1);
   // => size > 1

   gap_buffer_invariants(buffer);
}

// TODO: widen the contracts!!!!!!!!!
forceinline char
get_char_at_index(gap_buffer* buffer, cursor_position cursor_index)
{
   pre(buffer);
   pre(cursor_index < buffer->end - gap_size(buffer));
   pre(cursor_index != buffer->end);

   gap_buffer_invariants(buffer);

   buffer_position buffer_index = cursor_index < buffer->gap_begin ? cursor_index : cursor_index + gap_size(buffer);

   // wp(index < buffer->end)
   // wp(cursor < buffer->end)
   // (cursor < buffer->end)

   // wp(index < buffer->end)
   // wp(cursor + gap_size < buffer->end)
   // wp(cursor < buffer->end - gap_size)

   gap_buffer_invariants(buffer);

   post(buffer_index < buffer->end);
   return buffer->memory[buffer_index];
}

// TODO: widen the contracts? so that the callsite does not have to worry
// TODO: rename to indicate current state of cursor
forceinline char
get_char_at_cursor(gap_buffer* buffer)
{
   pre(buffer);
   pre(buffer->cursor <= buffer->end - gap_size(buffer));
   pre(buffer->cursor != buffer->end);

   gap_buffer_invariants(buffer);

   buffer_position index = buffer->cursor < buffer->gap_begin ? buffer->cursor : buffer->cursor + gap_size(buffer);


   // wp(index < buffer->end)
   // wp(cursor < buffer->end)
   // (cursor < buffer->end)

   // wp(index < buffer->end)
   // wp(cursor + gap_size < buffer->end)
   // wp(cursor < buffer->end - gap_size)

   gap_buffer_invariants(buffer);

   post(index < buffer->end);
   return buffer->memory[index];
}

function void
move_forwards(gap_buffer* buffer)
{
   pre(buffer);
   pre(buffer->cursor < buffer_size(buffer));

   gap_buffer_invariants(buffer);

   const buffer_position old_buffer_size = buffer_size(buffer);

   move_bytes(buffer->memory + buffer->gap_begin, buffer->memory + buffer->gap_end, 1);

   buffer->cursor++;

   buffer->gap_begin++;
   buffer->gap_end++;

   post(old_buffer_size == buffer_size(buffer));

   gap_buffer_invariants(buffer);
}

function void
move_backwards(gap_buffer* buffer)
{
   pre(buffer);
   pre(buffer->cursor != 0);

   gap_buffer_invariants(buffer);

   const buffer_position old_buffer_size = buffer_size(buffer);

   move_bytes(buffer->memory + buffer->gap_end - 1, buffer->memory + buffer->gap_begin - 1, 1);
   buffer->cursor--;

   buffer->gap_end--;
   buffer->gap_begin--;

   post(old_buffer_size == buffer_size(buffer));

   gap_buffer_invariants(buffer);
}

function void
set_cursor_to_begin_of_line(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);

   do
   {
      gap_buffer_invariants(buffer);
      if (buffer->cursor == 0)
      {
         return;
      }
      move_backwards(buffer);
   } while (get_char_at_cursor(buffer) != '\n');

   post(get_char_at_cursor(buffer) == '\n');

   move_forwards(buffer);

   gap_buffer_invariants(buffer);
}

function void
set_cursor_to_begin_of_next_line(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);

   if (buffer->cursor >= buffer->end - gap_size(buffer))
   {
      return;
   }

   while (get_char_at_cursor(buffer) != '\n')
   {
      gap_buffer_invariants(buffer);
      if (buffer->cursor >= buffer_size(buffer))
      {
         return;
      }
      move_forwards(buffer);
      if (buffer->cursor >= buffer->end - gap_size(buffer))
      {
         return;
      }
   }

   post(get_char_at_cursor(buffer) == '\n');

   move_forwards(buffer);

   set_cursor_to_begin_of_line(buffer);

   gap_buffer_invariants(buffer);
}

function void
set_cursor_to_end_of_line(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);

   // one past last cursor position
   if (buffer->cursor >= buffer_size(buffer))
   {
      return;
   }
   while (get_char_at_cursor(buffer) != '\n')
   {
      move_forwards(buffer);
      gap_buffer_invariants(buffer);
      // one past last cursor position
      if (buffer->cursor >= buffer_size(buffer))
      {
         return;
      }
      gap_buffer_invariants(buffer);
   }

   implies(buffer->cursor < buffer_size(buffer), get_char_at_cursor(buffer) == '\n');
   gap_buffer_invariants(buffer);
}

function void
set_cursor_to_begin_of_previous_line(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);

   set_cursor_to_begin_of_line(buffer);

   if (buffer->cursor != 0)
   {
      move_backwards(buffer);
   }

   set_cursor_to_begin_of_line(buffer);

   gap_buffer_invariants(buffer);
}

function bool
try_insert_character(gap_buffer* buffer, char c)
{
   pre(buffer);
   pre(buffer->end * 2 > 1 + buffer->gap_begin);

   gap_buffer_invariants(buffer);

   if (is_gap_full(buffer))
   {
      const buffer_position old_end = buffer->end;
      const buffer_position old_gap_end = buffer->gap_end;
      const buffer_position old_gap_begin = buffer->gap_begin;
      const buffer_position buffer_remnants = old_end - old_gap_end;

      const buffer_position new_buffer_size = old_end * 2 + buffer_remnants;

      const void* reallocted_memory = cast(HeapReAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, buffer->memory, new_buffer_size), byte*);

      if (!reallocted_memory)
      {
         de_initialize(buffer);

         return false;
      }

      buffer->memory = (byte*)reallocted_memory;

      buffer->end = new_buffer_size;
      buffer->gap_end = buffer->end - buffer_remnants;

      // shuffle the characters after the previous gap after new gap end.
      move_bytes(buffer->memory + buffer->gap_end, buffer->memory + old_gap_end, buffer_remnants);

      // new gap not full anymore.
      // wp(S, gap_size((buffer)) != 1)
      // wp(S, (gap_end - gap_begin) != 1)

      // wp(S, (new_buffer_size - buffer_remnants - gap_begin) != 1)
      // wp(S, (old_end * 2 + buffer_remnants - buffer_remnants - gap_begin) != 1)
      // wp(S, (old_end * 2 + old_end - old_gap_end - (old_end - old_gap_end) - gap_begin) != 1)
      // wp(S, (old_end * 2 + old_end - old_gap_end - old_end + old_gap_end - gap_begin) != 1)

      // wp(S, (old_end * 2 - gap_begin) != 1)
      // wp(S, old_end * 2 - gap_begin != 1)
      // wp(S, old_end * 2 != 1 + gap_begin)	== precond

      // wp(S, old_end * 2 != 1 + gap_begin)   == precond

      // wp(S, gap_end != 1 + gap_begin) == is_gap_full

      // wp(S, gap_end != old_end * 2) == ?

      post(!is_gap_full(buffer));

      // make sure old buffer remnants fit after the gap.
      // wp(S, buffer->gap_end == buffer->end - buffer_remnants)
      // wp(S, new_buffer_size - buffer_remnants == new_buffer_size - buffer_remnants)
      // wp(S, T)
      // T
      post(buffer->gap_end == buffer->end - buffer_remnants);

      // final new buffer size.
      post(new_buffer_size == old_end * 2 + buffer_remnants);
   }

   buffer->memory[buffer->gap_begin] = c;
   buffer->cursor++;

   buffer->gap_begin++;

   gap_buffer_invariants(buffer);

   return true;
}

function void
insert_newline(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);

   try_insert_character(buffer, '\n');

   gap_buffer_invariants(buffer);
}

function void
move_up(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);

   buffer_position column_cursor_index = buffer->cursor;

   set_cursor_to_begin_of_line(buffer);

   column_cursor_index = column_cursor_index - buffer->cursor;

   move_backwards(buffer);

   set_cursor_to_begin_of_line(buffer);

   while (column_cursor_index > 0)
   {
      move_forwards(buffer);
      --column_cursor_index;
   }

   //debug_message("column cursor: \t\t%d\n", column_cursor);

   gap_buffer_invariants(buffer);
}

function void
move_down(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);

   buffer_position gap_end = buffer->gap_end + 1;
   buffer_position gap_shift = 0;

   gap_buffer_invariants(buffer);
}

// fix similarly to moving backwards.
function void
backspace(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);
   const buffer_position old_buffer_size = buffer_size(buffer);

   // cant backspace anymore.
   if (buffer->cursor == 0)
   {
      return;
   }

   buffer->cursor--;

   buffer->gap_begin--;

   buffer->memory[buffer->gap_begin] = 0;

   post(old_buffer_size - 1 == buffer_size(buffer));

   gap_buffer_invariants(buffer);
}

function void
draw_cursor(f32 cursor_left, f32 cursor_top, f32 cursor_right, f32 cursor_bottom, D2D1_COLOR_F cursor_color)
{
   D2D1_ROUNDED_RECT cursor_rounded;
   D2D1_RECT_F cursor;

   cursor.left = cursor_left;
   cursor.top = cursor_top;
   cursor.right = cursor_right;
   cursor.bottom = cursor_bottom;

   cursor_rounded.rect = cursor;
   cursor_rounded.radiusX = 1.0f;
   cursor_rounded.radiusY = 1.0f;

   D2D1_COLOR_F old_color = global_text_brush->GetColor();
   global_text_brush->SetColor(&cursor_color);
   global_render_target->DrawRoundedRectangle(cursor_rounded, global_text_brush, 2.0f, NULL);
   global_text_brush->SetColor(&old_color);
}

function u32
get_white_space_count(gap_buffer* buffer)
{
   u32 result = 0;
   const cursor_position old_cursor = buffer->cursor;

   for (buffer->cursor = 0; buffer->cursor < buffer->end - gap_size(buffer); buffer->cursor++)
   {
      gap_buffer_invariants(buffer);
      {
         char c = get_char_at_cursor(buffer);
         isspace(c) ? result++ : result;
      }
      gap_buffer_invariants(buffer);
   }

   buffer->cursor = old_cursor;

   return result;
}

function u32
get_word_count(gap_buffer* buffer, cursor_position begin, cursor_position end)
{
   pre(buffer);
   pre(begin < end - gap_size(buffer));

   u32 result = 0;
   bool has_word_started = false;

   for (cursor_position cursor = begin; cursor != end; ++cursor)
   {
      switch (get_char_at_index(buffer, cursor))
      {
      case '\0': case ' ':
      case '\t': case '\n':
      case '\r': case '\r\n':
         if (has_word_started)
         {
            has_word_started = false;
            result++;
         }
         break;
      default: has_word_started = true;
      }
   }
   if (has_word_started)
   {
      has_word_started = false;
      result++;
   }

   return result;
}

function u32
get_word_count_in_line(gap_buffer* buffer)
{
   pre(buffer);
   gap_buffer_invariants(buffer);

   u32 result = 0;

   gap_buffer old_buffer = *buffer;

   set_cursor_to_end_of_line(buffer);
   cursor_position end_of_line_cursor = buffer->cursor;

   set_cursor_to_begin_of_line(buffer);
   cursor_position begin_of_line_cursor = buffer->cursor;

   result = get_word_count(buffer, begin_of_line_cursor, end_of_line_cursor);

   *buffer = old_buffer;

   gap_buffer_invariants(buffer);

   return result;
}

function void
layout(gap_buffer* buffer, f32 left, f32 top, f32 width, f32 height)
{
   gap_buffer_invariants(buffer);

   // TODO: s16 here
   byte utf8[1 << 16] = {};
   WCHAR utf16[1 << 16] = {};

   buffer->word_count = get_word_count_in_line(buffer);

   D2D1_RECT_F layout = {};
   layout.left = left;
   layout.top = top;
   layout.right = layout.left + width;
   layout.bottom = layout.top + height;

   // TODO: handle multibyte unicode advancements.

   buffer_position cursor = buffer->cursor;
   buffer_position utf_index = 0;
   const cursor_position pane_end = global_current_pane.end;
   for (cursor_position pane_cursor = global_current_pane.begin; pane_cursor != pane_end; pane_cursor++)
   {
      gap_buffer_invariants(buffer);

      if (pane_cursor < buffer->end - gap_size(buffer))
      {
         char c = get_char_at_index(buffer, pane_cursor);
         utf8[utf_index] = c;
         int char_count = MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)utf8 + utf_index, 1, utf16 + utf_index, 0);
         invariant(char_count <= 1 << 16);
         MultiByteToWideChar(CP_UTF8, 0, (LPCSTR)utf8 + utf_index, 1, utf16 + utf_index, char_count);
         utf_index++;
      }
      invariant(utf_index <= (1 << 16));
      gap_buffer_invariants(buffer);
   }

   if (global_text_layout)
      global_text_layout->Release();

   global_write_factory->CreateTextLayout(utf16, (UINT)wcslen(utf16), global_text_format, layout.right - layout.left, layout.bottom - layout.top, &global_text_layout);

   IDWriteRenderingParams* params = 0;
   HRESULT hr = global_write_factory->CreateCustomRenderingParams(
      2.2f,                     // gamma
      1.0f,                     // enhanced contrast
      1.0f,                     // ClearType level
      DWRITE_PIXEL_GEOMETRY_RGB, // pixel geometry
      DWRITE_RENDERING_MODE_CLEARTYPE_NATURAL, // rendering mode
      &params
   );

   if (SUCCEEDED(hr) && params)
   {
      global_render_target->SetTextRenderingParams(params);
      params->Release();
   }

   gap_buffer_invariants(buffer);
}

function void
draw(gap_buffer* buffer, f32 left, f32 top, f32 width, f32 height)
{
   if (width == 0 || height == 0)
      return;
   if (!global_text_layout)
      return;

   D2D1_RECT_F layout = {};
   layout.left = left;
   layout.top = top;
   layout.right = layout.left + width;
   layout.bottom = layout.top + height;

   gap_buffer_invariants(buffer);

   global_render_target->SetAntialiasMode(D2D1_ANTIALIAS_MODE_PER_PRIMITIVE);
   global_render_target->SetTextAntialiasMode(D2D1_TEXT_ANTIALIAS_MODE_CLEARTYPE);
   global_render_target->PushAxisAlignedClip(&layout, D2D1_ANTIALIAS_MODE_ALIASED);

   f32 dpix, dpiy;
   global_render_target->GetDpi(&dpix, &dpiy);
   assert(dpix == 96.f && dpiy == 96.f);

   f32 layout_left = layout.left;
   f32 layout_top = layout.top;

   f32 cursor_x = 0, cursor_y = 0;
   DWRITE_HIT_TEST_METRICS cursor_metrics = {};
   global_text_layout->HitTestTextPosition((u32)buffer->cursor, FALSE, &cursor_x, &cursor_y, &cursor_metrics);

   D2D1_POINT_2F origin = { layout.left, layout.top };
   global_render_target->DrawTextLayout(origin, global_text_layout, global_text_brush);

   f32 cursor_left = cursor_x + layout.left;
   f32 cursor_top = cursor_y + layout.top;
   f32 cursor_right = cursor_left + cursor_metrics.width;
   f32 cursor_bottom = cursor_top + cursor_metrics.height;

   D2D1_COLOR_F cursor_color = { 1.0f, 0.0f, 0.0f, 1.0f };

   if (cursor_metrics.width > 0 && cursor_metrics.height > 0)
      draw_cursor(cursor_left, cursor_top, cursor_right, cursor_bottom, cursor_color);
   else
   {
      cursor_color.b = 1.0f;
      cursor_color.g = 0.0f;
      draw_cursor(cursor_left, cursor_top + 37, cursor_left + 17, cursor_top + 35, cursor_color);
   }

   if (buffer->cursor < buffer->end - gap_size(buffer))
   {
      const char cursor_char = get_char_at_cursor(buffer);
      debug_message("cursor char: %c\n", (cursor_char) ? cursor_char : '0');
      //debug_message("\n");

      debug_message("cursor width: %d\n", (int)cursor_right - (int)cursor_left);
      debug_message("cursor height: %d\n", (int)cursor_bottom - (int)cursor_top);
   }

   // draw begin pane marker.
   if (0)
   {
      f32 cursor_x, cursor_y;
      DWRITE_HIT_TEST_METRICS cursor_metrics = {};
      global_text_layout->HitTestTextPosition((u32)global_current_pane.begin, FALSE, &cursor_x, &cursor_y, &cursor_metrics);
      cursor_left = cursor_x + layout.left;
      cursor_top = cursor_y + layout.top;
      cursor_right = cursor_left + cursor_metrics.width;
      cursor_bottom = cursor_top + cursor_metrics.height;

      const D2D1_COLOR_F color = { 0.0f, 1.0f, 0.0f, 1.0f };
      draw_cursor(cursor_left, cursor_top, cursor_right, cursor_bottom, color);
   }
   if (0)
   {
      // draw end pane marker.
      global_text_layout->HitTestTextPosition((u32)global_current_pane.end, FALSE, &cursor_x, &cursor_y, &cursor_metrics);
      cursor_left = cursor_x + layout.left;
      cursor_top = cursor_y + layout.top;
      cursor_right = cursor_left + cursor_metrics.width;
      cursor_bottom = cursor_top + cursor_metrics.height;

      const D2D1_COLOR_F color = { 1.0f, 0.0f, 0.0f, 1.0f };
      draw_cursor(cursor_left, cursor_top, cursor_right, cursor_bottom, color);
   }

   global_render_target->PopAxisAlignedClip();
   gap_buffer_invariants(buffer);
}

// TODO: fix cursor position in the pane scoll
function void
update_scroll_pane_view(gap_buffer* buffer, pane* scroll)
{
   pre(buffer);
   pre(scroll);

   gap_buffer_invariants(buffer);
   scroll_pane_invariants(scroll, buffer);

   // cursor must always be in the current scroll region: [begin, end)
   if (buffer->cursor < scroll->begin)
   {
      return;
   }
   post(buffer->cursor >= scroll->begin);

   if (buffer->cursor >= scroll->end)
   {
      return;
   }
   post(buffer->cursor < scroll->end);

   scroll_pane_invariants(scroll, buffer);
   gap_buffer_invariants(buffer);
}

function void
load_test_file(gap_buffer* buffer)
{
   pre(buffer);
}

function uint2
get_editor_window_size(HWND window_handle)
{
   uint2 result = {};

   RECT rect;
   if (GetClientRect(window_handle, &rect))
   {
      int width = rect.right - rect.left;
      int height = rect.bottom - rect.top;

      result.x = width;
      result.y = height;
   }
   return result;
}

// TODO: Input thread for keys
LRESULT CALLBACK
sys_window_proc(HWND window, UINT message, WPARAM w_param, LPARAM l_param)
{
   LRESULT result = 0;

   gap_buffer* buffer = (gap_buffer*)(void*)GetWindowLongPtr(window, GWLP_USERDATA);

   if (buffer)
   {
      switch (message)
      {
      case WM_DESTROY:
      {
         global_quit = true;
      } break;
      case WM_SIZE:
      {
         RECT client_rect;
         GetClientRect(window, &client_rect);
         D2D1_SIZE_U window_size;
         window_size.width = client_rect.right - client_rect.left;
         window_size.height = client_rect.bottom - client_rect.top;
         if (global_render_target)
            global_render_target->Release();
         GlobalD2D1Factory->CreateHwndRenderTarget(D2D1::RenderTargetProperties(), D2D1::HwndRenderTargetProperties(window, window_size), &global_render_target);
         if (global_text_brush)
            global_text_brush->Release();
         global_render_target->CreateSolidColorBrush(D2D1::ColorF(D2D1::ColorF::Black), &global_text_brush);
      } break;
#if 0
      case WM_CHAR:
      {
         {
            u32 vk_code = (u32)w_param;
            b32 was_down = (l_param & (1ll << 30)) != 0;
            b32 is_down = (l_param & (1ll << 31)) == 0;

            if (vk_code == 0x0d)
            {
               insert_newline(buffer);
            }
            else if (vk_code == VK_BACK)
            {
               backspace(buffer);
            }
            else if (vk_code == '0')
            {
               set_cursor_to_begin_of_line(buffer);
            }
            else if (vk_code == '$')
            {
               set_cursor_to_end_of_line(buffer);
            }
#if 0
            else if (vk_code == 'h')
            {
               scroll_pane_invariants(&global_current_pane, buffer);
               // scroll forward
               // TODO: should probably be global_current_pane.end < buffersize(buffer)
               if (global_current_pane.Begin < global_current_pane.end && global_current_pane.end < buffer->end)
               {
                  ++global_current_pane.end;
                  ++global_current_pane.Begin;
               }

               scroll_pane_invariants(&global_current_pane, buffer);
               //invariant(begin++, end++, scroll->Begin < scroll->end);
               //invariant(scroll->Begin + 1 < scroll->end + 1);
               //invariant(scroll->Begin < scroll->end );
            }
            else if (vk_code == 'l')
            {
               scroll_pane_invariants(&global_current_pane, buffer);
               // scroll back
               if (global_current_pane.Begin > 0)
               {
                  --global_current_pane.Begin;
                  --global_current_pane.end;
               }
               scroll_pane_invariants(&global_current_pane, buffer);
            }
#endif
            else
            {
               // cleanup
               {
                  const int buffer_size = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&w_param, 1, 0, 0, 0, 0);

                  char multi_bytes[16] = {};

                  const int result = WideCharToMultiByte(CP_UTF8, 0, (WCHAR*)&w_param, 1, multi_bytes, buffer_size, 0, 0);

                  // remove the <= 2 byte assumption.
                  // multibyte chars.
                  // TODO: test the booleans.
                  if (result == 2)
                  {
                     try_insert_character(buffer, multi_bytes[0]);
                     try_insert_character(buffer, multi_bytes[1]);
                  }
                  else if (result == 1)
                     try_insert_character(buffer, multi_bytes[0]);
               }
            }
         }
      } break;
      case WM_KEYDOWN:
      {
         switch (w_param)
         {
         case VK_LEFT:
            if (buffer->cursor != 0)
            {
               move_backwards(buffer);
            }
            break;
         case VK_RIGHT:
            if (buffer->cursor < buffer_size(buffer))
            {
               move_forwards(buffer);
            }
            break;
         case VK_DOWN:
         {
            // TODO: scroll down by the amount it gets to next newline from scroll pane begin if exists
            // TODO: right now just scroll by fixed amount for testing
            const usize scroll_count = 6;
            if (scroll_size(&global_current_pane) > scroll_count)
            {
               global_current_pane.begin += scroll_count;
            }
            scroll_pane_invariants(&global_current_pane, buffer);

            // wp(begin += 5, begin < end)
            // wp(begin + 5 < end)
            // wp(5 < end - begin)
         }
         break;
         case VK_UP:
         {
            // TODO: scroll up by the amount it gets to next newline if exists
            if (0 < global_current_pane.end - global_current_pane.begin + 6 && global_current_pane.begin >= 6)
            {
               global_current_pane.begin -= 6;
            }
            scroll_pane_invariants(&global_current_pane, buffer);

            // case1:
            // wp(begin -= 5, begin < end && begin >= 0)
            // wp(begin - 5 < end && begin - 5 >= 0)

            // wp(begin < end + 5 && begin >= 5)

            // wp(0 < end - begin + 5 && begin >= 5)

            // wp(0 < end - begin + 5 && begin >= 5)
         }
         break;
         case VK_END:
            load_test_file(buffer);
            break;
         }
      } break;
#endif
      default:
      {
         result = DefWindowProc(window, message, w_param, l_param);
         break;
      }
      }
      return result;
   }

   return DefWindowProc(window, message, w_param, l_param);
}

static void set_window_title(HWND handle, const char* message, ...)
{
   static char buffer[512];

   va_list args;
   va_start(args, message);

   vsprintf_s(buffer, sizeof(buffer), message, args);

   SetWindowTextA(handle, buffer);

   va_end(args);
}

function void input_gather(gap_buffer* buffer, f64 total_seconds_elapsed)
{
   static bool prev_down[256] = {};

   const f64 key_down_interval = 0.16666666667f; // ~167ms - 10 frames of delay in 60 FPS
   //const f64 key_down_interval = 0.333333333333333f; // ~333ms - 20 frames of delay in 60 FPS

   for(int vk = 'A'; vk <= 'Z'; ++vk)
   {
      u32 key_state = GetAsyncKeyState(vk);

      bool is_down = (key_state & 0x8000) != 0;
      bool was_pressed = is_down && !prev_down[vk];

      u32 ch = MapVirtualKeyA(vk, MAPVK_VK_TO_CHAR);

      // Caps Lock is toggle state — 0x0001 bit of GetKeyState
      bool caps = (GetKeyState(VK_CAPITAL) & 0x0001) != 0;
      // Shift is physical state — 0x8000 bit of GetAsyncKeyState
      bool shift = (GetAsyncKeyState(VK_SHIFT) & 0x8000) != 0;

      if(!(shift ^ caps))
         ch = (char)tolower(ch);

      if(was_pressed)
      {
         f64 delta_seconds = total_seconds_elapsed - buffer->time_since_last_insert[vk];
         if(delta_seconds > key_down_interval)
         {
            try_insert_character(buffer, (char)ch);
            buffer->time_since_last_insert[vk] = total_seconds_elapsed;
            printf("Pressed timestamp: %f\n", buffer->time_since_last_insert[vk]);
         }
      }
      else if(is_down)
      {
         f64 delta_seconds = total_seconds_elapsed - buffer->time_since_last_insert[vk];
         if(delta_seconds > key_down_interval)
         {
            try_insert_character(buffer, (char)ch);
            printf("Is Down timestamp: %f\n", total_seconds_elapsed);
         }
      }

      prev_down[vk] = is_down;
   }

   {
      const usize vk = VK_BACK;
      u32 key_state = GetAsyncKeyState(vk);
      bool is_down = (key_state & 0x8000) != 0;
      bool was_pressed = is_down && !prev_down[vk];

      if(was_pressed)
      {
         f64 delta_seconds = total_seconds_elapsed - buffer->time_since_last_insert[vk];
         if(delta_seconds > key_down_interval)
         {
            backspace(buffer);
            buffer->time_since_last_insert[vk] = total_seconds_elapsed;
         }
      }
      else if(is_down)
      {
         f64 delta_seconds = total_seconds_elapsed - buffer->time_since_last_insert[vk];
         if(delta_seconds > key_down_interval)
            backspace(buffer);
      }
      prev_down[vk] = is_down;
   }

   {
   if(buffer->cursor != 0)
   {
      const usize vk = VK_LEFT;
      u32 key_state = GetAsyncKeyState(vk);
      bool is_down = (key_state & 0x8000) != 0;
      bool was_pressed = is_down && !prev_down[vk];

      if(was_pressed)
      {
         buffer->time_since_last_insert[vk] = total_seconds_elapsed;
         move_backwards(buffer);
      }
      else if(is_down)
      {
         f64 delta_seconds = total_seconds_elapsed - buffer->time_since_last_insert[vk];
         if(delta_seconds > key_down_interval)
            move_backwards(buffer);
      }
      prev_down[vk] = is_down;
   }
   }

   {
   if(buffer->cursor < buffer_size(buffer))
   {
      const usize vk = VK_RIGHT;
      u32 key_state = GetAsyncKeyState(vk);
      bool is_down = (key_state & 0x8000) != 0;
      bool was_pressed = is_down && !prev_down[vk];

      if(was_pressed)
      {
         buffer->time_since_last_insert[vk] = total_seconds_elapsed;
         move_forwards(buffer);
      }
      else if(is_down)
      {
         f64 delta_seconds = total_seconds_elapsed - buffer->time_since_last_insert[vk];
         if(delta_seconds > key_down_interval)
            move_forwards(buffer);
      }
      prev_down[vk] = is_down;
   }
   }

   #if 0
   // TODO: Do the time delta thing for these too
   if(GetAsyncKeyState(VK_RIGHT) & key_state_pressed)
      if(buffer->cursor < buffer_size(buffer))
         move_forwards(buffer);

   if(GetAsyncKeyState(VK_RETURN) & key_state_pressed)
      insert_newline(buffer);

   if(GetAsyncKeyState(VK_SPACE) & key_state_pressed)
      try_insert_character(buffer, ' ');
   #endif
}

int main()
{
   clock_query_frequency();

   gap_buffer gap_buffer = {};

   const usize buffer_size = 1 << 16;

   // TODO: reasonable intial buffer size - just for testing now
   initialize(&gap_buffer, buffer_size);

   // TODO: change the values to cover the entire pane
   // TODO: think about the pane range
   global_current_pane.begin = gap_buffer.cursor;
   global_current_pane.end = buffer_size;

   // COM stuff.
   {
      HRESULT DWriteResult = D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED, &GlobalD2D1Factory);
      DWriteResult = DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED, __uuidof(IDWriteFactory), (IUnknown**)&global_write_factory);
      DWriteResult = global_write_factory->CreateTextFormat(L"Consolas", 0, DWRITE_FONT_WEIGHT_SEMI_BOLD, DWRITE_FONT_STYLE_NORMAL, DWRITE_FONT_STRETCH_NORMAL, 30.0f, L"en-us", &global_text_format);
      global_text_format->SetWordWrapping(DWRITE_WORD_WRAPPING_NO_WRAP);
   }

   {
      WNDCLASS window_class = {};
      window_class.hInstance = 0;
      window_class.lpfnWndProc = sys_window_proc;
      window_class.lpszClassName = L"zed";
      window_class.style = CS_OWNDC | CS_HREDRAW | CS_VREDRAW;
      ATOM window_class_atom = RegisterClass(&window_class);

      invariant(window_class_atom);
   }

   // adjust the client area related to the screen origin + client size.
   int x = 100;
   int y = 100;
   int width = 800;
   int height = 600;
   RECT desired_window = { x, y, width, height };
   AdjustWindowRect(&desired_window, WS_OVERLAPPEDWINDOW, FALSE);
   HWND window_handle = CreateWindow(L"zed", L"editor", WS_OVERLAPPEDWINDOW, desired_window.left, desired_window.top, desired_window.right, desired_window.bottom, 0, 0, 0, 0);

   invariant(window_handle);

   // TODO: attach pane or do a pointer to the current buffer inside the pane structure.
   SetWindowLongPtr(window_handle, GWLP_USERDATA, (LONG_PTR)&gap_buffer);

   UpdateWindow(window_handle);
   ShowWindow(window_handle, SW_SHOW);

   HWND console = GetConsoleWindow();
   ShowWindow(console, SW_HIDE);

   s64 begin = clock_query_counter();
   f64 total_seconds_elapsed = 0;

   while (!global_quit)
   {
      MSG message;
      while(PeekMessage(&message, 0, 0, 0, PM_REMOVE))
      {
         TranslateMessage(&message);
         DispatchMessage(&message);
      }

      update_scroll_pane_view(&gap_buffer, &global_current_pane);

      input_gather(&gap_buffer, total_seconds_elapsed);

      uint2 window_size = get_editor_window_size(window_handle);

      layout(&gap_buffer, 0, 0, (f32)window_size.x, (f32)window_size.y);

      global_render_target->BeginDraw();
      global_render_target->Clear(D2D1::ColorF(D2D1::ColorF::LightBlue));

      draw(&gap_buffer, 0, 0, (f32)window_size.x, (f32)window_size.y);

      frame_sync(0.01666666666666666666666666666667 / 1);

      s64 end = clock_query_counter();

      HRESULT draw_result = global_render_target->EndDraw();
      if(draw_result != S_OK)
         return -1;

      f64 seconds_elapsed = clock_seconds_elapsed(begin, end);
      total_seconds_elapsed += seconds_elapsed;

      begin = end;

      set_window_title(window_handle, "FPS: %u", (u32)((1.f / seconds_elapsed) + .5f));
   }

   de_initialize(&gap_buffer);

   return 0;
}