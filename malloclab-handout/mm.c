/*
 * 
 *
 * Simple linked list for tracking  free space
 * There is coalescing for previous and next blocks
 * Payloads have Headers and footers
 * Pages have prologs
 *
 * Mswenson U0585863
 */
 
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* block header : payload size, previous free block ptr*/
typedef struct {
  size_t size;
  void * prev_free;
} block_header;

/* footer: size, next free *Only for unallocated*/
typedef struct {
  size_t size;
  void *next_free;
} block_footer;

/* Page Header: ptrs: previous page next page*/
typedef struct {
  void *prev_page;
  void *next_page;
} page_header;

/* Each page has a prolog after the page header */
typedef struct {
  size_t size;
  size_t page_size;
} prolog;

/* always use 16-byte alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~(ALIGNMENT-1))

/*Size of block_header*/
#define BLOCK_OVERHEAD (sizeof(block_header))

#define HEADER_PAYLOAD(b_payload) ((char*)(b_payload) - sizeof(block_header))

/* Get payload size */
#define GET(p) (*(size_t *)(p))

/* Check if Free */
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Overhead + Payload size */
#define GET_SIZE(p) (GET(p) & ~0xF)

/*Get Allocation Previous Block*/
#define GET_PREV_ALLOC(p) (GET(p) & 0x2)

/*Add data*/
#define INSERT(p, val) (*(size_t*)(p) = (val))

#define FOOTER_PAYLOAD(b_payload) ((char*)(b_payload) + (GET_SIZE(HEADER_PAYLOAD(b_payload)) - sizeof(block_header) - sizeof(block_footer)))

#define NEXT_PAY(b_payload) ((char*)(b_payload) + GET_SIZE(HEADER_PAYLOAD(b_payload)))

#define PREV_FT(b_payload) ((char*)(b_payload) - sizeof(block_header) - sizeof(block_footer))

/* Setup size, allocation, and previous allocation */
#define SET_BITS(size, alloc, prev_alloc) ((size) | (alloc) | (prev_alloc))

/* Footer Ptr next free block*/
#define NEXT_FREE(b_payload) ((block_footer*)(FOOTER_PAYLOAD(b_payload)))->next_free

/* Header->prev */ 
#define PREV_FREE(b_payload) ((block_header*) (HEADER_PAYLOAD(b_payload)))->prev_free

/*Previous payload if free*/
#define PREV_BLKP(b_payload) ((char*)(b_payload) - GET_SIZE(PREV_FT(b_payload)))



/*********  PAGE  MACROS *******************/

/* Similar to ALIGN but for pages */
#define PAGE_ALIGN(size) (((size) + (mem_pagesize()-1)) & ~(mem_pagesize()-1))

#define PAGE_NEXT(ph) ((page_header*)(ph))->next_page
#define PAGE_PREV(ph) ((page_header*)(ph))->prev_page

/*First payload on page*/
#define PAGE_FIRST_PAY(ph) ((char*)(ph) + PAGE_OVERHEAD - BLOCK_OVERHEAD)

#define PAGE_OVERHEAD (sizeof(page_header) + BLOCK_OVERHEAD + BLOCK_OVERHEAD + BLOCK_OVERHEAD)

#define PAGE_PROLOG(ph) ((char*)(ph) + sizeof(page_header))

static void allocate_mem(void *b_payload, size_t size);
static void *coalesce(void *b_payload);
static void remove_free(void *b_payload);
static void add_free(void *b_payload);
static void remove_page(void *b_payload);

/* first block payload pointer */
static void *first_pay;
static void *last_freed;
static void *first_page;

/* minimum size of a page request */
static int min_page_size;

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  min_page_size = (mem_pagesize()*7);
  size_t size = min_page_size;

  //Initialize page
  first_page = mem_map(size);
  PAGE_PREV(first_page) = 0;
  PAGE_NEXT(first_page) = 0;

  // Create prolog
  INSERT(HEADER_PAYLOAD(PAGE_PROLOG(first_page)), SET_BITS(32, 0x1, 0x3));
  ((prolog*)(PAGE_PROLOG(first_page)))->page_size = size;

  // Add first payload
  first_pay = PAGE_FIRST_PAY(first_page);
  INSERT(HEADER_PAYLOAD(first_pay), SET_BITS(size - PAGE_OVERHEAD, 0x0, 0x2));
  INSERT(FOOTER_PAYLOAD(first_pay), SET_BITS(size - PAGE_OVERHEAD, 0x0, 0x2));

  //Init Free list ptrs
  NEXT_FREE(first_pay) = 0;
  PREV_FREE(first_pay) = 0;
  last_freed = first_pay;

  // Create end block
  void *b_payload = NEXT_PAY(first_pay);
  INSERT(HEADER_PAYLOAD(b_payload), SET_BITS(0, 0x1, 0x00));

  return 0;
}

/********* HELPER *************/

/*
 * Create new Page
 */
static void *new_page(size_t size) 
{
  void *lp, *pp, *b_payload;
  int current_avail_size = 0;

  // Calculate if we need a bigger page than the minimum
  if (size < (min_page_size - PAGE_OVERHEAD))
  {    
    current_avail_size = min_page_size;
  }
  else
  {
    current_avail_size = PAGE_ALIGN(size + PAGE_OVERHEAD);
    min_page_size = current_avail_size*25;
  }

  // find the last page
  lp = first_page;
  while (PAGE_NEXT(lp) != NULL)
  {
    lp = PAGE_NEXT(lp);
  }
  
  //Link new page
  pp = mem_map(current_avail_size);
  PAGE_NEXT(lp) = pp;
  PAGE_PREV(pp) = lp;
  PAGE_NEXT(pp) = 0;

  INSERT(HEADER_PAYLOAD(PAGE_PROLOG(pp)), SET_BITS(32, 0x1, 0x3));
  ((prolog*)(PAGE_PROLOG(first_page)))->page_size = current_avail_size;

  //Setup payload
  b_payload = PAGE_FIRST_PAY(pp);
  INSERT(HEADER_PAYLOAD(b_payload), SET_BITS(current_avail_size - PAGE_OVERHEAD, 0x0, 0x2));
  INSERT(FOOTER_PAYLOAD(b_payload), SET_BITS(current_avail_size - PAGE_OVERHEAD, 0x0, 0x2));

  // Free list management
  add_free(b_payload);

  b_payload = NEXT_PAY(b_payload);
  INSERT(HEADER_PAYLOAD(b_payload), SET_BITS(0, 0x1, 0x00));
  
  return PAGE_FIRST_PAY(pp);
}

/* 
 * mm_malloc - Allocate a block by using bytes from current_avail,
 *     grabbing a new page if necessary.
 */
void *mm_malloc(size_t size)
{
  // Align the given size 
  int new_size = ALIGN(size + BLOCK_OVERHEAD);
  void *b_payload;

  // If last_freed== 0, pages are full
  if (last_freed != 0)
  {
    b_payload = last_freed;
    do
    {
  	  if (!GET_ALLOC(HEADER_PAYLOAD(b_payload)) && (GET_SIZE(HEADER_PAYLOAD(b_payload)) >= new_size))
      {
        allocate_mem(b_payload, new_size);
        return b_payload;
      }
  	  b_payload = NEXT_FREE(b_payload);
    } while (b_payload != 0);
  }

  //New page if no blocks big enough
  b_payload = new_page(new_size);

  // Add to new page
  allocate_mem(b_payload, new_size);
  return b_payload;
}

/************ HELPER ***************/

/*
 * allocate_mem - assigns value to block
 */
static void allocate_mem(void *b_payload, size_t size)
{
  size_t extra_space = GET_SIZE(HEADER_PAYLOAD(b_payload)) - size;

  // Remove this block from the free list
  remove_free(b_payload);

  //Check for split
  if (extra_space > ALIGN(1 + BLOCK_OVERHEAD))
  {
    INSERT(HEADER_PAYLOAD(b_payload), SET_BITS(size, 0x1, 0x2));    
    INSERT(HEADER_PAYLOAD(NEXT_PAY(b_payload)), SET_BITS(extra_space, 0x0, 0x2));
    INSERT(FOOTER_PAYLOAD(NEXT_PAY(b_payload)), SET_BITS(extra_space, 0x0, 0x2));

    //Track block in free list
    add_free(NEXT_PAY(b_payload));
  }

  //Didn't split
  else 
  {
  	INSERT(HEADER_PAYLOAD(b_payload), SET_BITS(GET_SIZE(HEADER_PAYLOAD(b_payload)), 0x1, 0x2));
  	INSERT(HEADER_PAYLOAD(NEXT_PAY(b_payload)), SET_BITS(GET_SIZE(HEADER_PAYLOAD(NEXT_PAY(b_payload))), 0x1, 0x2));
  }
}

/*
 * mm_free - Now With Coalescing 49.99$ *
 */
void mm_free(void *b_payload)
{

  INSERT(HEADER_PAYLOAD(b_payload), SET_BITS(GET_SIZE(HEADER_PAYLOAD(b_payload)), 0x0, GET_PREV_ALLOC(HEADER_PAYLOAD(b_payload))));
  INSERT(FOOTER_PAYLOAD(b_payload), SET_BITS(GET_SIZE(HEADER_PAYLOAD(b_payload)), 0x0, GET_PREV_ALLOC(HEADER_PAYLOAD(b_payload))));

  b_payload = coalesce(b_payload);

  INSERT(HEADER_PAYLOAD(NEXT_PAY(b_payload)), SET_BITS(GET_SIZE(HEADER_PAYLOAD(NEXT_PAY(b_payload))), 0x1, 0x0));

  // Erase page if there is only one block
  if (GET_SIZE(NEXT_PAY(b_payload)) == 0 && GET_PREV_ALLOC(PREV_FT(b_payload)) == 3)
  {
    remove_page(b_payload);
  }
}

/*
 * Check if needed, check next, prev or both
 */
static void *coalesce(void *b_payload)
{
  size_t prev_alloc = GET_PREV_ALLOC(HEADER_PAYLOAD(b_payload));
  size_t next_alloc = GET_ALLOC(HEADER_PAYLOAD(NEXT_PAY(b_payload)));
  size_t size = GET_SIZE(HEADER_PAYLOAD(b_payload));


  //Don't coalesce
  if (prev_alloc && next_alloc)
  {
    add_free(b_payload);
  }
  //Coalesce next block
  else if (prev_alloc && !next_alloc)
  {
     //Remove block from the free list
    remove_free(NEXT_PAY(b_payload));

    //Coalesce
    size += GET_SIZE(HEADER_PAYLOAD(NEXT_PAY(b_payload)));
    INSERT(HEADER_PAYLOAD(b_payload), SET_BITS(size, 0x0, 0x2));
    INSERT(FOOTER_PAYLOAD(b_payload), SET_BITS(size, 0x0, 0x2));

    add_free(b_payload);
  }
  //Coalesce previous
  else if (!prev_alloc && next_alloc)
  {    
    //Previous block removed
    remove_free(PREV_BLKP(b_payload));

    //Combine
    size += GET_SIZE(PREV_FT(b_payload));
    INSERT(FOOTER_PAYLOAD(b_payload), SET_BITS(size, 0x0, 0x2));
    INSERT(HEADER_PAYLOAD(PREV_BLKP(b_payload)), SET_BITS(size, 0x0, 0x2));
    b_payload = PREV_BLKP(b_payload);

    add_free(b_payload);
  }
  //Coalesce both
  else if (!prev_alloc && !next_alloc)
  {
    //Same pattern
    remove_free(PREV_BLKP(b_payload));
    remove_free(NEXT_PAY(b_payload));

    size += GET_SIZE(HEADER_PAYLOAD(NEXT_PAY(b_payload))) + GET_SIZE(PREV_FT(b_payload));
    INSERT(HEADER_PAYLOAD(PREV_BLKP(b_payload)), SET_BITS(size, 0x0, 0x2));
    INSERT(FOOTER_PAYLOAD(NEXT_PAY(b_payload)), SET_BITS(size, 0x0, 0x2));
    b_payload = PREV_BLKP(b_payload);

    add_free(b_payload);
  }
 
  return b_payload;
}

/*
 * add_free(b_payload) - Add a given block to the list of unallocated blocks
 */
static void add_free(void *b_payload)
{
  if (last_freed == 0) 
  {
    NEXT_FREE(b_payload) = 0;
    PREV_FREE(b_payload) = 0;
    last_freed = b_payload;
  }
  else 
  {
	NEXT_FREE(b_payload) = last_freed;
    PREV_FREE(b_payload) = 0;
    PREV_FREE(last_freed) = b_payload;
    last_freed = b_payload;
  }
}

/*
 * remove_free(b_payload)- it is gone or allocated
 */
static void remove_free(void *b_payload)
{
  if ((PREV_FREE(b_payload) == 0) && (NEXT_FREE(b_payload) == 0))
  {    
  	last_freed = 0;
  }
  else if (PREV_FREE(b_payload) == 0)
  {
  	PREV_FREE(NEXT_FREE(b_payload)) = 0;
    last_freed = NEXT_FREE(b_payload);
  }
  else if (NEXT_FREE(b_payload) == 0)
  {
   	NEXT_FREE(PREV_FREE(b_payload)) = 0;
  }
  else 
  {
    NEXT_FREE(PREV_FREE(b_payload)) = NEXT_FREE(b_payload);
  	PREV_FREE(NEXT_FREE(b_payload)) = PREV_FREE(b_payload);
  }	
}

/*
 * remove_page - Stop tracking 
 */
static void remove_page(void *b_payload)
{
  void *pp = ((char *)(b_payload) - PAGE_OVERHEAD + BLOCK_OVERHEAD);
  if ((PAGE_PREV(pp) == 0) && (PAGE_NEXT(pp) == 0))
  {
    return;
  }
  else if (PAGE_PREV(pp) == 0)
  {
    PAGE_PREV(PAGE_NEXT(pp)) = 0;
    first_page = PAGE_NEXT(pp);
  }
  else if (PAGE_NEXT(pp) == 0)
  {
    PAGE_NEXT(PAGE_PREV(pp)) = 0;
  }
  else 
  {
    PAGE_NEXT(PAGE_PREV(pp)) = PAGE_NEXT(pp);
    PAGE_PREV(PAGE_NEXT(pp)) = PAGE_PREV(pp);
  }
  mem_unmap(pp, ((prolog*)(PAGE_PROLOG(first_page)))->page_size);
}