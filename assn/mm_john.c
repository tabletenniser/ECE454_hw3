/*
 * This implementation replicates the implicit list implementation
 * provided in the textbook
 * "Computer Systems - A Programmer's Perspective"
 * Blocks are never coalesced or reused.
 * Realloc is implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
    "PrinterOnFire",
    /* First member's full name */
    "Jun Tao Luo",
    /* First member's email address */
    "jt.luo@mail.utoronto.ca",
    /* Second member's full name (leave blank if none) */
    "Chang Liu",
    /* Second member's email address (leave blank if none) */
    "cha.liu@mail.utoronto.ca"
};

/*************************************************************************
 * Basic Constants and Macros
 * You are not required to use these macros but may find them helpful.
 *************************************************************************/
#define WSIZE       sizeof(void *)      /* word size (bytes) */
#define DSIZE       (2 * WSIZE)         /* doubleword size (bytes) */
#define MINBSIZE    (2 * DSIZE)         /* minimum memory block size (bytes) */
#define CHUNKSIZE   (1<<7)              /* initial heap size (bytes) */
#define FREE_LISTS  30                  /* number of free lists */
#define SEARCH_LIM  100                 /* cut-off for free blocks to search within each free list */
#define ROUND_SIZE  32                  /* the multiple to round up to when extending the heap */

#define MAX(x,y) ((x) > (y) ? (x) : (y))
#define MIN(x,y) ((x) < (y) ? (x) : (y))

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

/* Given free block ptr bp, compute address of pointers to the next and previous blocks */
#define PREVP(bp)        ((char *)(bp))
#define NEXTP(bp)        ((char *)(bp) + WSIZE)

/* Given free block ptr bp, compute address of next and previous free blocks */
#define PREV_FREE_BLKP(bp) ((char *)GET(PREVP(bp)))
#define NEXT_FREE_BLKP(bp) ((char *)GET(NEXTP(bp)))

/* Mark the current block as allocated or free with specified size */
#define mark_alloc(bp, size)    do { PUT(HDRP(bp), PACK(size, 1)); PUT(FTRP(bp), PACK(size, 1)); } while (0)
#define mark_free(bp, size)     do { PUT(HDRP(bp), PACK(size, 0)); PUT(FTRP(bp), PACK(size, 0)); } while (0)
#define mark_epilogue(bp)       PUT(HDRP(bp), PACK(0, 1))

/* Debug level, used for log */
#define DEBUG_LEVEL 0
#define log(level, args ...)    do { if(level <= DEBUG_LEVEL){ printf(args); printf("\n"); } } while (0)

/* Global pointers */
void* heap_listp = NULL;        // First block of the heap
void* free_listp[FREE_LISTS];   // List of free blocks segregated by size

/*+========================================================+
 *| Helpers                                                |
 *+========================================================+*/

// /**********************************************************
//  * log
//  * Debug logging utility. Prints out the message specified
//  * by args with a new line at the end. Only messages with
//  * levels smaller than the DEBUG_LEVEL will be displayed.
//  **********************************************************/
// void log(size_t level, args ...) 
// {
//     if (level <= DEBUG_LEVEL) { 
//         printf(args); 
//         printf("\n"); 
//     }
// }
// 
// /**********************************************************
//  * mark_alloc
//  * Mark the current block as allocated with the given size
//  **********************************************************/
// void mark_alloc(void *bp, size_t size)
// {
//     PUT(HDRP(bp), PACK(size, 1));
//     PUT(FTRP(bp), PACK(size, 1));
// }
// 
// /**********************************************************
//  * mark_free
//  * Mark the current block as allocated with the given size
//  **********************************************************/
// void mark_free(void *bp, size_t size)
// {
//     PUT(HDRP(bp), PACK(size, 0));
//     PUT(FTRP(bp), PACK(size, 0));
// }

/**********************************************************
 * get_free_list_index
 * Return the free list that a free block of given size
 * belongs to
 **********************************************************/
size_t get_free_list_index(size_t x)
{
    /* The free list has exponential bins (4-7, 8-15, ...) 
     * TODO: an improvement is to use linear bins for small
     * sizes and exponential bins for large sizes */
    log(1, "Function: get_free_list_index");
    
    /* The smallest bucket has 4 words available*/
    x >>= 2;

    /* Compute the index as the floor of the binary log */
    size_t pos = 0;
    if (x > 1<<16) { x >>= 16; pos += 16; }
    if (x > 1<< 8) { x >>=  8; pos +=  8; }
    if (x > 1<< 4) { x >>=  4; pos +=  4; }
    if (x > 1<< 2) { x >>=  2; pos +=  2; }
    if (x > 1<< 1) {           pos +=  1; }

    log(2, "Free block of size %zx goes into free list %zd", x, pos);

    return pos;
}

/**********************************************************
 * round_up
 * Return the given number rounded up to the nearest
 * multiple of ROUND_SIZE
 **********************************************************/
size_t round_up (size_t x)
{
    x -= DSIZE;
    x = ((x/ROUND_SIZE)+1)*ROUND_SIZE + DSIZE; 
    return x;
}

/**********************************************************
 * insert_free_block
 * Insert the given free block in the appropriate free list
 * at the front
 **********************************************************/
void insert_free_block(void *bp)
{
    /* TODO: Check if keeping the free list sorted by size improves performance */
    log(1, "Function: insert_free_block");

    size_t free_list_index = get_free_list_index(GET_SIZE(HDRP(bp)));

    /* Put the block at the front of the appropriate free list */
    if (free_listp[free_list_index]) PUT(PREVP(free_listp[free_list_index]), (uintptr_t)bp);
    PUT(NEXTP(bp), (uintptr_t)free_listp[free_list_index]);
    PUT(PREVP(bp), (uintptr_t)NULL);
    free_listp[free_list_index] = bp;
}

/**********************************************************
 * remove_free_block
 * Removes the free block from the explicit free list
 **********************************************************/
void remove_free_block(void *bp)
{
    log(1, "Function: remove_free_block");
    log(2, "Address %p prev %zx next %zx", bp, GET(PREVP(bp)), GET(NEXTP(bp)));
    
    size_t free_list_index = get_free_list_index(GET_SIZE(HDRP(bp)));

    if (GET(PREVP(bp)) && GET(NEXTP(bp))) {
        /* There are free blocks before and after bp */
        PUT(PREVP(NEXT_FREE_BLKP(bp)), GET(PREVP(bp)));
        PUT(NEXTP(PREV_FREE_BLKP(bp)), GET(NEXTP(bp)));
    }
    else if (GET(NEXTP(bp))) { 
        /* This is the first free block */
        PUT(PREVP(NEXT_FREE_BLKP(bp)), (uintptr_t)NULL);
        free_listp[free_list_index] = (char *)GET(NEXTP(bp));
    }
    else if (GET(PREVP(bp))) {
        /* This is the last free block */
        PUT(NEXTP(PREV_FREE_BLKP(bp)), (uintptr_t)NULL);
    }
    else {
        /* This is the only free block */
        free_listp[free_list_index] = (char *)NULL;
    }
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
    log(1, "Function: coalesce");
    log(2, "Previous block address %p header %zx, Next block address %p header %zx", PREV_BLKP(bp), GET(HDRP(PREV_BLKP(bp))), NEXT_BLKP(bp), GET(HDRP(NEXT_BLKP(bp))));

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
       
    /* Case 1 */
    if (prev_alloc && next_alloc) {
        /* No coalescing */
        log(2, "case 1");
    }
    /* Case 2 */
    else if (prev_alloc && !next_alloc) {
        log(2, "case 2");

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        /* Splice out the next free block */
        remove_free_block(NEXT_BLKP(bp));
        
        /* Update header */
        mark_free(bp, size);
    }
    /* Case 3 */
    else if (!prev_alloc && next_alloc) {
        log(2, "case 3");

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        
        /* Splice out the previous free block */
        remove_free_block(PREV_BLKP(bp));
        
        /* Update header */
        bp = PREV_BLKP(bp);
        mark_free(bp, size);
    }
    /* Case 4 */
    else {
        log(2, "case 4");

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
        
        /* Splice out the previous and next free block */
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));

        /* Update header */
        bp = PREV_BLKP(bp);
        mark_free(bp, size);
    }
    
    /* Put the coalesced freed block in front (LIFO) */
    insert_free_block(bp);

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
    log(1, "Function: extend_heap");

    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignments */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ( (bp = mem_sbrk(size)) == (void *)-1 )
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    mark_free(bp, size);
    mark_epilogue(NEXT_BLKP(bp));

    /* Put the freed block in front (LIFO) */
    insert_free_block(bp);
    
    log(2, "extending by %zx", size);

    return bp;
}

/**********************************************************
 * find_fit
 * Traverse the heap searching for the best block to fit 
 * asize. To save time, impose a limit on how far to search.
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
void * find_fit(size_t asize)
{
    log(1, "Function: find_fit");

    size_t free_list_index, search_count;
    void *bp;

    /* Search the free lists for that would contain a free block of the required size or larger*/
    for (free_list_index = get_free_list_index(asize); free_list_index < FREE_LISTS; free_list_index++) 
    {
        /* Keep track of current free block, best free block and blocks searched */
        bp = free_listp[free_list_index];
        search_count = 0;
        void *best_bp;
        size_t best_bp_size = 9999999;

        /* Only search up to the number of blocks specified by SEARCH_LIM */
        while (bp != NULL && search_count < SEARCH_LIM) 
        {

            log(3, "Scanning %p of size %zx with prev ptr %p and next ptr %p", bp, GET_SIZE(HDRP(bp)), (void *)GET(PREVP(bp)), (void *)GET(NEXTP(bp)));
            /* Update best if block is larger than the requested asize and smaller than the previous best */
            if (asize <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) < best_bp_size) 
            {
                best_bp = bp;
                best_bp_size = GET_SIZE(HDRP(bp));
            }
            
            bp = (void *)GET(NEXTP(bp));
            search_count++;
        }

        if (best_bp) return best_bp;
    }

    /* Default to no block found */    
    return NULL;
}

/**********************************************************
 * place
 * Mark the block as allocated
 **********************************************************/
void place(void* bp, size_t asize)
{
    log(1, "Function: place");

    /* Get the current block size */
    size_t bsize = GET_SIZE(HDRP(bp));

    remove_free_block(bp);

    /* Check if there is sufficient space for a free block after allocation*/
    if (bsize - asize >= MINBSIZE) {
        /* Create an allocated block of size asize*/
        mark_alloc(bp, asize);
        
        /* Create a free block for the unused space*/
        mark_free(NEXT_BLKP(bp), bsize - asize);
        
        /* Put the free block in front (LIFO) */
        insert_free_block(NEXT_BLKP(bp));

        log(2, "split into %p of size %zx and %p of size %zx", bp, asize, NEXT_BLKP(bp), bsize-asize);
    }
    else {
        /* Can't split free block so allocate entire free block */
        mark_alloc(bp, bsize);
    }
}

/*+========================================================+
 *| Core Functions                                         |
 *+========================================================+*/

/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
int mm_init(void)
{
    log(1, "\nUser Function: mm_init");

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                         // alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header
    heap_listp += DSIZE;

    /* Initialize free lists */
    size_t i;
    for (i = 0; i < FREE_LISTS; i++)
        free_listp[i] = (char *)NULL;

    return 0;
}


/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
    log(1, "\nUser Function: mm_free - %p", bp);
    log(2, "freeing %p header %zx footer %zx", bp, GET(HDRP(bp)), GET(FTRP(bp)));

    if(bp == NULL){
        return;
    }

    mark_free(bp, GET_SIZE(HDRP(bp)));
    coalesce(bp);
}

/**********************************************************
 * mm_malloc
 * Allocate a block of size bytes.
 * The type of search is determined by find_fit
 * The decision of splitting the block, or not is determined
 *   in place(..)
 * If no block satisfies the request, the heap is extended
 **********************************************************/
void *mm_malloc(size_t size)
{
    log(1, "\nUser Function: mm_malloc - %zx", size);

    size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char * bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = MINBSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    /* Round up the asize to the nearest multiple of ROUND_SIZE */
    extendsize = round_up(asize);
    log(1, "rounded %zx to %zx", asize, extendsize);

    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    
    log(2, "allocated block of size %zx at %p", asize, bp);
    
    return bp;

}

/**********************************************************
 * mm_realloc
 * Implemented simply in terms of mm_malloc and mm_free
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
    log(1, "\nUser Function: mm_realloc - %p, %zx", ptr, size);

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0){
        mm_free(ptr);
        return NULL;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL)
        return (mm_malloc(size));

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t oldsize = GET_SIZE(HDRP(oldptr));

    //TODO handle extending to the next block if it is free
    //TODO consider freeing up this memory in some cases
    if (3 + DSIZE + size < oldsize)
    {
        log(2, "Old size is enough");
        return oldptr;
    }

    /* Check if the ptr is the last block in the heap */
    if (GET(HDRP(NEXT_BLKP(oldptr))) == 1)
    {
        log(2, "This is the last block, only heap extension necessary");

        /* In this case just extend the heap by the necessary amount */
        size_t words = (3 + DSIZE + size - oldsize)/WSIZE;
        size_t extendsize = (words % 2) ? (words+1) * WSIZE : (words) * WSIZE;
        void *bp;

        if ( (bp = mem_sbrk(extendsize)) == (void *)-1 )
            return NULL;

        /* Update block header/footer and the epilogue header */
        mark_alloc(oldptr, oldsize + extendsize);
        mark_epilogue(NEXT_BLKP(oldptr));
        
        log(2, "extending current block at %p of size %zx. Current header %zx, next block header is %zx", oldptr, oldsize, GET(HDRP(oldptr)), GET(HDRP(NEXT_BLKP(oldptr))));
        
        return oldptr;
    }
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    /* Copy the old data. */
    copySize = GET_SIZE(HDRP(oldptr));
    memcpy(newptr, oldptr, MIN(copySize, size));
    mm_free(oldptr);

    log(2, "reallocated block of size %zx at %p", GET_SIZE(HDRP(newptr)), newptr);

    return newptr;
}

/**********************************************************
 * mm_check
 * Check the consistency of the memory heap
 * Return nonzero if the heap is consistant.
 *********************************************************/
int mm_check(void)
{
    log(1, "\nUser Function: mm_check");

    printf("checking heap consistency\n");

    return 1;
}
