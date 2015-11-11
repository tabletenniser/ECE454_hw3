/*
This file implements dynamic memory allocation functions (i.e malloc, free and
realloc) using the segregated free list with the following high-level details:
  1) An array of linkedlist (free_block_lists[]) is used to keep track of free
     blocks of different sizes. free_block_lists[i] contains free blocks of size
     1<<(i+SHIFT_SIZE) bytes. For example, if SHIFT_SIZE=2,then free_block_lists[6]
     contains free blocks greater than 256 bytes but less than 512 bytes.
  2) Two extra words are allocated for each free block after the header for the
     pointers to the next free block and previous free block. Theses two words locate
     right after the HEADER section of each block.
  3) mm_realloc() implmentation is changed such that if the new size is smaller than
     the current block, then return the same block ptr and do not do "free() and malloc()".
  4) mm_realloc() is also changed such that if the block is at the end of the heap, it extends
     the heap and return the same pointer passed in instead of doing "free() and malloc()".
     This solves the runtime blow up for realloc-bal.rep.
*/
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "LOL",
    /* First member's full name */
    "Zexuan Wang",
    /* First member's email address */
    "zexuan.wang@mail.utoronto.ca",
    /* Second member's full name (leave blank if none) */
    "Yiming Kang",
    /* Second member's email address (leave blank if none) */
    "yiming.kang@mail.utoronto.ca"
};

/*************************************************************************
 * Basic Constants and Macros
 * You are not required to use these macros but may find them helpful.
*************************************************************************/
#define WSIZE       sizeof(void *)            /* word size (bytes) */
#define DSIZE       (2 * WSIZE)            /* doubleword size (bytes) */
#define CHUNKSIZE   (1<<5)      /* initial heap size (bytes) = 32 bytes, four words. This used to be 1<<7*/
#define NUM_OF_FREE_LISTS 30
#define LIMIT 1

#define MAX(x,y) ((x) > (y)?(x) :(y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
/* Read and write a word at address p */
#define GET(p)          (*(uintptr_t *)(p))
#define PUT(p,val)      (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of pointers to next and previous blocks */
#define PREV_FREE_BLKP(bp)  ((char*)bp)
#define NEXT_FREE_BLKP(bp)  ((char*)bp + WSIZE)

/* Logging utility macros */
#define LOGGING_LEVEL 0     // Max is 6.
#define logg(level, args ...)    if(level <= LOGGING_LEVEL){ printf(args); printf("\n"); fflush(stdout);}

/* Global heap pointer */
void* heap_listp = NULL;
// An array of free blocks organized by sizes growed exponentially.
void* free_block_lists[NUM_OF_FREE_LISTS];


/*******************************************************************************************
********************************************************************************************
************************************* DEBUGGING FUNCTIONS **********************************
********************************************************************************************
*******************************************************************************************/

/* OLD LOGGING FUNCTION (replaced by logg() macro above): Logging utility to bypass the stdout buffer, print out the message immediately */
void logg_old(int level, char *arg, ...){
    if (level <= LOGGING_LEVEL){
        printf(arg);
        printf("\n");
        fflush(stdout);
    }
}

/**********************************************************
 * mm_check
 * Check the consistency of the memory heap and free block list.
 * Print error message and return nonzero if the heap is consistant.
 *********************************************************/
int mm_check(void){
    int i = 0;
    char *iter;
    int fail = 0;

    // Iterate through the list of free blocks and check: 1) un-aligned blocks; 2) in-consistant
    // footer / header and 3) blocks that are not free.
    for (i = 0; i<NUM_OF_FREE_LISTS; i++){
        iter = free_block_lists[i];
        while (iter!=NULL) {
            if ((size_t)iter%8){
                printf("FREEBLOCK ERROR: UN-ALIGNED BLOCK. bp: %p\n", iter);
                fail = 1;
                break;
            }
            if (GET(FTRP(iter)) != GET(HDRP(iter))) {
                printf("FREEBLOCK ERROR: INCONSISTANCY FOOTER / HEADER. index: %d; bp: %p; header: %zx; footer: %zx\n", i, iter, GET(HDRP(iter)), GET(FTRP(iter)));
                fail = 1;
                break;
            }
            if (GET_ALLOC(HDRP(iter))) {
                printf("FREEBLOCK ERROR: BLOCK NOT FREE. index: %d; bp: %p; header: %zx", i, iter, GET(HDRP(iter)));
                fail = 1;
                break;
            }
            iter = (char *)GET(NEXT_FREE_BLKP(iter));
        }
    }
    if (fail == 1){
        printf("************** mm_check() FAILS!!!!!! ***********");
        return 1;
    }

    // Iterate through the entire heap and check: 1) bp pointer actually lies inside the heap
    // allocated using mem_sbrk(); 2) un-aligned blocks; 2) in-consistant footer / header;
    // 3) free blocks that are not in the free list and 4) contiguour free blocks not coalesced.
    void* start_heap = mem_heap_lo();
    void* end_heap = mem_heap_hi();
    for (iter = (char *)start_heap + DSIZE; GET_SIZE(HDRP(iter)) > 0; iter=NEXT_BLKP(iter)){
        if (iter < (char *)start_heap) {
            printf("HEAP ERROR: BLOCK POINTER BEFORE START OF HEAP. bp: %p\n", iter);
            fail = 1;
            break;
        }
        if (iter > (char *)end_heap) {
            printf("HEAP ERROR: BLOCK POINTER AFTER END OF HEAP. bp: %p\n", iter);
            fail = 1;
            break;
        }
        if ((size_t)iter%8){
            printf("HEAP ERROR: UN-ALIGNED BLOCK. bp: %p\n", iter);
            fail = 1;
            break;
        }
        if (GET(FTRP(iter)) != GET(HDRP(iter))) {
            printf("HEAP ERROR: INCONSISTANCY FOOTER / HEADER. bp: %p; header: %zx; footer: %zx\n", iter, GET(HDRP(iter)), GET(FTRP(iter)));
            fail = 1;
            break;
        }
        if (!GET_ALLOC(HDRP(iter)) && !GET_ALLOC(HDRP(NEXT_BLKP(iter)))) {
            printf("HEAP ERROR: CONTIGUOUS FREE BLOCKS FOUND. bp: %p; header: %zx; bp.next: %p; bp.next.header: %zx\n", iter, GET(HDRP(iter)), NEXT_BLKP(iter), GET(HDRP(NEXT_BLKP(iter))));
            fail = 1;
            break;
        }


    }
    if (fail == 1){
        printf("************** mm_check() FAILS!!!!!! ***********");
        return 1;
    }
    return 0;
}

/**********************************************************
 * print_free_lists
 * Iterates through the array of free blocks with different sizes.
 * Print the list of free blocks at each index.
 *********************************************************/
void print_free_lists(){
    int i = 0;
    char *iter;
    printf("========== The free block lists ==========\n");
    for (i = 0; i<NUM_OF_FREE_LISTS; i++){
        iter = free_block_lists[i];
        printf("%d: ", i);
        while (iter!=NULL) {
            printf("%p(header:%zx;size:%zx)\t", iter, GET(HDRP(iter)), GET_SIZE(HDRP(iter)));
            iter = (char *)GET(NEXT_FREE_BLKP(iter));
            if (iter!=NULL)
                printf("%p\t", iter);
        }
        printf("\n");
    }
}


/*******************************************************************************************
********************************************************************************************
************************************** UTILITY FUNCTIONS ***********************************
********************************************************************************************
*******************************************************************************************/

/**********************************************************
 * add_free_block
 * utility function that inserts the bp block to the
 * linkedlist of free blocks.
 *********************************************************/
void add_free_block(void *bp){
    logg(4, "============ add_free_block() starts ==============");

    // Find the proper index to insert the block.
    int free_list_i = 0;
    int size = GET_SIZE(HDRP(bp));
    while (size > (1 << (free_list_i))){
        free_list_i++;
    }

    // Add block from bp to the linkedlist of free_block_lists.
    if (free_block_lists[free_list_i])
        PUT(PREV_FREE_BLKP(free_block_lists[free_list_i]), (uintptr_t)bp);
    PUT(NEXT_FREE_BLKP(bp), (uintptr_t)free_block_lists[free_list_i]);
    PUT(PREV_FREE_BLKP(bp), (uintptr_t)NULL);
    free_block_lists[free_list_i]=bp;

    logg(5, "free_list_i is: %d; size is: %d; bp is: %p", free_list_i, size, bp);
    logg(5, "next of bp is: %zx; prev of bp is: %zx", GET(NEXT_FREE_BLKP(bp)), GET(PREV_FREE_BLKP(bp)));
    logg(4, "============ add_free_block() ends ==============");
    return;
}

/**********************************************************
 * remove_free_block
 * utility function that removes the bp block to the
 * linkedlist of free blocks.
 *********************************************************/
void remove_free_block(void *bp){
    logg(4, "============ remove_free_block() starts ==============");
    logg(5, "bp: %p;prev blk ptr: %zx;next blk ptr: %zx", bp, GET(PREV_FREE_BLKP(bp)), GET(NEXT_FREE_BLKP(bp)));

    // Find the proper index where the block should locates.
    int free_list_i = 0;
    int size = GET_SIZE(HDRP(bp));
    while (size > (1 << (free_list_i))){
        free_list_i++;
    }

    // Remove the block from the doubly-linked linkedlist.
    char *next_block_ptr = (char *)GET(NEXT_FREE_BLKP(bp));
    char *prev_block_ptr = (char *)GET(PREV_FREE_BLKP(bp));
    // Case for only one free block
    if (!GET(PREV_FREE_BLKP(bp)) && !GET(NEXT_FREE_BLKP(bp))){
        logg(5, "Case A: block is the only free block in the list");
        free_block_lists[free_list_i] = NULL;
    }
    // Case where bp is the first free block
    else if (!GET(PREV_FREE_BLKP(bp)) && GET(NEXT_FREE_BLKP(bp))){
        logg(5, "Case B: block is the first free block in the list");
        PUT(PREV_FREE_BLKP(next_block_ptr), (uintptr_t)NULL);
        free_block_lists[free_list_i] = next_block_ptr;
    }
    // Case where bp is the last free block
    else if (GET(PREV_FREE_BLKP(bp)) && !GET(NEXT_FREE_BLKP(bp))){
        logg(5, "Case C: block is the last free block in the list");
        PUT(NEXT_FREE_BLKP(prev_block_ptr), (uintptr_t)NULL);
    }
    // Case where free blocks exist both before and after bp.
    else {
        logg(5, "Case D: free block exists in both directions");
        PUT(NEXT_FREE_BLKP(prev_block_ptr), (uintptr_t)NULL);
        PUT(PREV_FREE_BLKP(next_block_ptr), (uintptr_t)NULL);
    }
    logg(4, "============ remove_free_block() ends ==============");
    return;
}

/**********************************************************
 * coalesce
 * Covers the 4 cases discussed in the text:
 * - both neighbours are allocated
 * - the next block is available for coalescing
 * - the previous block is available for coalescing
 * - both neighbours are available for coalescing
 **********************************************************/
void *coalesce(void *bp)
{
    logg(4, "============ coalesce() starts ==============");
    logg(1, "coalesce() called with bp: %p; Previous block: %p header: %zx; Next block: %p header: %zx", bp, PREV_BLKP(bp), GET(HDRP(PREV_BLKP(bp))), NEXT_BLKP(bp), GET(HDRP(NEXT_BLKP(bp))));

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {       /* Case 1 */
        logg(2, "Case 1: Both prev and next blocks are allocated. NO coalescing.");
    }
    else if (prev_alloc && !next_alloc) { /* Case 2 */
        logg(2, "Case2: Next block is free.");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_free_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 */
        logg(2, "Case3: Prev block is free.");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_free_block(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);     // move bp one block ahead
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else {            /* Case 4 */
        logg(2, "Case4: Both blocks are free.");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  + GET_SIZE(HDRP(NEXT_BLKP(bp)))  ;
        remove_free_block(NEXT_BLKP(bp));
        remove_free_block(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
    }

    // Add the bp block to the beginning of free list of corresponding size.
    add_free_block(bp);
    logg(4, "============ coalesce() ends ==============");
    return bp;
}

/**********************************************************
 * extend_heap
 * Extend the heap by "words" words, maintaining alignment
 * requirements of course. Free the former epilogue block
 * and reallocate its new header
 **********************************************************/
void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignments */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ( (bp = mem_sbrk(size)) == (void *)-1 )
        return NULL;

    logg(1, "extend_heap extends words: %zx(h)(size: %zx(h)); new bp: %p", words, size, bp);
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));                // free block header
    PUT(FTRP(bp), PACK(size, 0));                // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));        // new epilogue header
    add_free_block(bp);
    return bp;
}

/**********************************************************
 * find_fit
 * Traverse the heap searching for a block to fit asize
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
void * find_fit(size_t asize)
{
    void *bp, *smallest_bp = (void *)NULL;
    int free_list_i=0;
    int count = 0;
    size_t smallest_bp_size = (size_t)-1;   // set to max size_t
    for (free_list_i = 1; free_list_i<NUM_OF_FREE_LISTS; free_list_i++){
        if ((1<<(free_list_i))<asize){
            continue;
        }
        /* printf("free_list_i is: %d", free_list_i); */
        bp = free_block_lists[free_list_i];
        count = 0;
        while (bp != NULL && count < LIMIT){
            count ++;
            if (asize <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) < smallest_bp_size){
                logg(1, "find_fit() finds a fittable block at: %p for size: %zx(h)%zu(d)", bp, asize, asize);
                /* return bp; */
                smallest_bp = bp;
                smallest_bp_size = GET_SIZE(HDRP(bp));
            }
        }
        if (smallest_bp!=NULL)
            return smallest_bp;
    }
    logg(2, "find_fit() cannot find a free block with proper size: %zx(h)%zu(d).", asize, asize);
    return NULL;
}

/**********************************************************
 * place
 * Mark the block as allocated.
 * Also create a new free block of the size difference if possible.
 **********************************************************/
void place(void* bp, size_t asize)
{
    remove_free_block(bp);
    /* Get the current block size */
    size_t bsize = GET_SIZE(HDRP(bp));

    // Create a block of the size difference and insert it into the free list.
    if (bsize - asize > 8*DSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(bsize-asize, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(bsize-asize, 0));
        add_free_block(NEXT_BLKP(bp));
    } else {
        PUT(HDRP(bp), PACK(bsize, 1));
        PUT(FTRP(bp), PACK(bsize, 1));
    }
}


/*******************************************************************************************
********************************************************************************************
***************************************** MAIN FUNCTIONS ***********************************
********************************************************************************************
*******************************************************************************************/

/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue. It allocates four words and
 * set the heap_listp pointer to the beginning of third word.
 **********************************************************/
int mm_init(void)
{
    logg(1, "============ mm_init() starts ==============");
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                         // alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header
    heap_listp += DSIZE;
    logg(1, "initial heap_listp: %p", heap_listp);
    // Initialize the segregated free lists.
    int i;
    for (i = 0; i < NUM_OF_FREE_LISTS; i++)
        free_block_lists[i]=NULL;
    logg(3, "============ mm_init() ends ==============");

    return 0;
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
    logg(3, "\n============ mm_free() starts ==============");
    if (LOGGING_LEVEL>0)
        mm_check();
	logg(1, "mm_free() with bp: %p; header: %zx(h); footer: %zx(h)", bp, GET(HDRP(bp)), GET(FTRP(bp)));
    if(bp == NULL){
      return;
    }

    // Mark the current block as free and do coalescing.
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);

    logg(3, "============ mm_free() ends ==============\n");
}


/**********************************************************
 * mm_malloc
 * Allocate a block of size bytes.
 * First search through the segregated free list to see if
 * there's a free block that fits. If so, return the block
 * pointer of the free block and create a new free block from
 * the difference. (in place() utility function)
 * If no block satisfies the request, the heap is extended
 **********************************************************/
void *mm_malloc(size_t size)
{
    logg(3, "\n============ mm_malloc() starts ==============");
    if (LOGGING_LEVEL>0)
        mm_check();
    size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char * bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);

    // Align it the other way to calibrate for binary-bal.rep.
    if (asize % 32 == 0)
        asize += DSIZE;

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    logg(1, "mm_malloc(%zx(h)%zu(d)) returns bp: %p; with actual size: %zx", size, size, bp, asize);
    if (LOGGING_LEVEL>0)
        mm_check();
    logg(3, "============ mm_malloc() ends ==============\n");
    return bp;

}

/**********************************************************
 * mm_realloc
 * If the size is smaller than the original block, simply
 * return the original block.
 * If the block is at the end of the heap, extend the heap
 * to the required size and return. (This is a calibraion
 * for realloc-bal.rep)
 * Otherwise, simply call mm_free() and mm_malloc().
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
    logg(3, "\n============ mm_realloc() starts ==============");
    if (LOGGING_LEVEL>0)
        mm_check();
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0){
      mm_free(ptr);
      return NULL;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL)
      return (mm_malloc(size));

    // If we can fit the new size into the old block, do it!
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t oldSize = GET_SIZE(HDRP(oldptr));
    size_t asize;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
    asize += DSIZE;     // For the prev / next free block.
    if (asize < oldSize) {
        logg(2, "Old pointer is enough. bp: %p; oldSize: %zx; newSize: %zx", oldptr, oldSize, asize);
        logg(3, "============ mm_realloc() ends ==============\n");
        return oldptr;
    }

    // Extend the heap if it's the last element. Calibaration for realloc-bal.rep trace.
    if (GET_SIZE(HDRP(NEXT_BLKP(oldptr))) == 0){
        mm_check();
        logg(2, "Last block, will extend the heap. bp: %p; oldSize: %zx; newSize: %zx", oldptr, oldSize, asize);
        size_t words = asize / WSIZE;
        asize = (words%2) ? (words+1) * WSIZE : words * WSIZE;
        void *bp;

        if ( (bp = mem_sbrk(asize-oldSize)) == (void *)-1 )
            return NULL;
        PUT(HDRP(oldptr), PACK(asize, 1));
        PUT(FTRP(oldptr), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(oldptr)), PACK(0, 1));
        mm_check();
        logg(3, "============ mm_realloc() ends ==============\n");
        return oldptr;
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    /* Copy the old data. */
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    logg(3, "============ mm_realloc() ends ==============\n");
    return newptr;
}
