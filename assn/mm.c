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
/* #define CHUNKSIZE   (1<<7)      #<{(| initial heap size (bytes) = 128 bytes|)}># */
#define CHUNKSIZE   (1<<4)      /* initial heap size (bytes) = 16 bytes, two words*/
#define NUM_OF_FREE_LISTS 30
#define SHIFT_SIZE 2

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

#define PREV_FREE_BLKP(bp)  ((char*)bp)
#define NEXT_FREE_BLKP(bp)  ((char*)bp + WSIZE)

#define LOGGING_LEVEL 0
/* #define LOGGING_LEVEL 6 */
#define logg(level, args ...)    if(level <= LOGGING_LEVEL){ printf(args); printf("\n"); fflush(stdout);}

void* heap_listp = NULL;        // Global heap pointer
void* free_block_lists[NUM_OF_FREE_LISTS];     // An array of free blocks organized by sizes

/* Logging utility to bypass the stdout buffer, print out the message immediately */
/* void logg(int level, char *arg, ...){ */
/* 	if (level <= LOGGING_LEVEL){ */
/* 		printf(arg); */
/* 		printf("\n"); */
/* 		#<{(| fflush(stdout); |)}># */
/* 	} */
/* } */

/**********************************************************
 * mm_check
 * Check the consistency of the memory heap
 * Return nonzero if the heap is consistant.
 *********************************************************/
int mm_check(void){
    int i = 0;
    char *iter;
    int fail = 0;
    for (i = 0; i<NUM_OF_FREE_LISTS; i++){
        iter = free_block_lists[i];
        /* while (iter!=NULL) { */
        if (iter!=NULL) {
            if (GET(FTRP(iter)) != GET(HDRP(iter))) {
                printf("index: %d; bp: %p; header: %zx; footer: %zx", i, iter, GET(HDRP(iter)), GET(FTRP(iter)));
               fail = 1;
               break;
            }
            if (GET_ALLOC(HDRP(iter))) {
                printf("index: %d; bp: %p; header: %zx", i, iter, GET(HDRP(iter)));
                fail = 1;
                break;
            }
            if (GET_ALLOC(FTRP(iter))) {
                printf("index: %d; bp: %p; footer: %zx", i, iter, GET(FTRP(iter)));
                fail = 1;
                break;
            }
            iter = (char *)GET(NEXT_FREE_BLKP(iter));
            if (iter!=NULL){
                if (GET(FTRP(iter)) != GET(HDRP(iter))) {
                    printf("index: %d; bp: %p; header: %zx; footer: %zx", i, iter, GET(HDRP(iter)), GET(FTRP(iter)));
                    fail = 1;
                    break;
                }
                if (GET_ALLOC(HDRP(iter))) {
                    printf("index: %d; bp: %p; header: %zx", i, iter, GET(HDRP(iter)));
                    fail = 1;
                    break;
                }
                if (GET_ALLOC(FTRP(iter))) {
                    printf("index: %d; bp: %p; footer: %zx", i, iter, GET(FTRP(iter)));
                    fail = 1;
                    break;
                }
            }
        }
    }
    if (fail == 1){
        printf("************** mm_check() FAILS!!!!!! ***********");
        return 1;
    }
    return 0;
}

void print_free_lists(){
    int i = 0;
    char *iter;
    printf("========== The free block lists ==========\n");
    for (i = 0; i<NUM_OF_FREE_LISTS; i++){
        iter = free_block_lists[i];
        printf("%d: ", i);
        /* while (iter!=NULL) { */
        if (iter!=NULL) {
            printf("%p\t", iter);
            iter = (char *)GET(NEXT_FREE_BLKP(iter));
            if (iter!=NULL)
                printf("%p\t", iter);
        }
        printf("\n");
    }
}

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

void add_free_block(void *bp){
    logg(4, "============ add_free_block() starts ==============");
    int free_list_i = 0;
    int size = GET_SIZE(HDRP(bp));
    while (size > (1 << (free_list_i+SHIFT_SIZE))){
        free_list_i++;
    }
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

// TODO: COMMENT
void remove_free_block(void *bp){
    logg(4, "============ remove_free_block() starts ==============");
    logg(5, "bp: %p;prev blk ptr: %zx;next blk ptr: %zx", bp, GET(PREV_FREE_BLKP(bp)), GET(NEXT_FREE_BLKP(bp)));
    int free_list_i = 0;
    int size = GET_SIZE(HDRP(bp));
    while (size > (1 << (free_list_i+SHIFT_SIZE))){
        free_list_i++;
    }
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
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  + GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
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

    /* Coalesce if the previous block was free */
    /* return coalesce(bp); */
}


/**********************************************************
 * find_fit
 * Traverse the heap searching for a block to fit asize
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
void * find_fit(size_t asize)
{
    void *bp;
    int free_list_i=0;
    /* for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) */
    /* { */
    /*     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) */
    /*     { */
    /*         logg(1, "find_fit() finds a fittable block at: %p for size: %zx(h)%zu(d)", bp, asize, asize); */
    /*         return bp; */
    /*     } */
    /* } */
    for (free_list_i = 0; free_list_i<NUM_OF_FREE_LISTS; free_list_i++){
        // 1<<(free_list_i+2) so that free_block_lists[0] contains the free blocks of size 4 words.
        if ((1<<(free_list_i+SHIFT_SIZE-1))<asize){
            continue;
        }
        bp = free_block_lists[free_list_i];
        while (bp != NULL){
            if (asize <= GET_SIZE(HDRP(bp))){
                logg(1, "find_fit() finds a fittable block at: %p for size: %zx(h)%zu(d)", bp, asize, asize);
                return bp;
            }
        }
    }
    logg(2, "find_fit() cannot find a free block with proper size: %zx(h)%zu(d).", asize, asize);
    return NULL;
}

/**********************************************************
 * place
 * Mark the block as allocated
 **********************************************************/
void place(void* bp, size_t asize)
{
    remove_free_block(bp);
  /* Get the current block size */
  size_t bsize = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(bsize, 1));
  PUT(FTRP(bp), PACK(bsize, 1));
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
    logg(3, "============ mm_free() starts ==============");
	logg(1, "mm_free() with bp: %p; header: %zx(h); footer: %zx(h)", bp, GET(HDRP(bp)), GET(FTRP(bp)));
    mm_check();
    if(bp == NULL){
      return;
    }
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp);
    logg(3, "============ mm_free() ends ==============");
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
    mm_check();
    logg(3, "============ mm_malloc() starts ==============");
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
    asize += DSIZE;     // For the prev / next free block.

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    mm_check();
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    mm_check();
    place(bp, asize);
    logg(1, "mm_malloc(%zx(h)%zu(d)) returns bp: %p; with actual size: %zx", size, size, bp, asize);
    logg(3, "============ mm_malloc() ends ==============");
    mm_check();
    return bp;

}

/**********************************************************
 * mm_realloc
 * Implemented simply in terms of mm_malloc and mm_free
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
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
    size_t oldSize = GET_SIZE(HDRP(oldptr));
    if (2*DSIZE + size < oldSize)
        return oldptr;

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    /* Copy the old data. */
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
