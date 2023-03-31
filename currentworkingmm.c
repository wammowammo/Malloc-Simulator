/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * A program that dynamically allocates memory so that the programmer can
 * use the memory to store data or create data structures.
 *
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author William Chen <wchen4@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = 2 * dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 13);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

static const word_t prev_alloc_mask = 0x2;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;
    /** @brief A pointer to the block payload. */
    union {
        struct {
            struct block *next;
            struct block *prev;
        };
        char payload[0];
    };
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

static const size_t topval = 12;

static block_t *seglist[topval];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */

static word_t pack(size_t size, bool alloc, bool prev_alloc){
    word_t word = size;
    if (alloc){
        word |= alloc_mask;
    }
    if(prev_alloc){
        word |= prev_alloc_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - dsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

static bool extract_prev_alloc(word_t word){
    return (bool)((word & prev_alloc_mask)>>1);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

static bool get_prev_alloc(block_t *block){
    return extract_prev_alloc(block->header);
}


/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, false);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool alloc, bool prevalloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc, prevalloc);
    if(!alloc){
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc, prevalloc);
    }
    
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

// find the index in the seglist given a bytesize (take log base 2 of a number)
static size_t find_root(size_t size) {
    if (size <= min_block_size) {
        return 0;
    } else {
        for (size_t i = 1; i < topval - 1; i++) {
            if (size < (min_block_size << (i + 1))) {
                return i;
            }
        }
    }
    return topval - 1;
}

// insert an empty block into the seglist
static void add_to_free(block_t *block) {

    size_t blocksize = get_size(block);
    size_t starter = find_root(blocksize);
    if (seglist[starter] == NULL) { // if list is empty
        seglist[starter] = block;
        block->next = NULL;
        block->prev = NULL;
    } else { // if list is not empty
        seglist[starter]->prev = block;
        block->next = seglist[starter];
        block->prev = NULL;
        seglist[starter] = block;
    }
}

// remove an element from the seglist
static void remove_from_free(block_t *removed) {
    size_t blocksize = get_size(removed);
    size_t starter = find_root(blocksize);

    if (removed->prev == NULL &&
        removed->next == NULL) { // its only item in the list
        seglist[starter] = NULL;
    } else if (removed->prev == NULL &&
               removed->next != NULL) { // if first element in it
        seglist[starter] = removed->next;
        seglist[starter]->prev = NULL;
    } else if (removed->next == NULL &&
               removed->prev != NULL) { // last element in list
        removed->prev->next = NULL;
    } else { // if its in the middle of list
        removed->prev->next = removed->next;
        removed->next->prev = removed->prev;
    }
}

/**
 * @brief
 *
 * Coalesces neighboring blocks if they are also free.
 * Takes in a block
 * returns a bigger block
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {
    bool prevalloc = get_prev_alloc(block);
    block_t *previous;
    block_t *next = find_next(block);
    if(!prevalloc){
        previous = find_prev(block);
    }
    size_t currsize = get_size(block);
    if (!prevalloc && previous!=NULL) { // prev empty
        size_t prevsize = get_size(previous);
        if (next != NULL && !get_alloc(next)) { // next empty
            remove_from_free(previous);
            remove_from_free(next);
            size_t size = prevsize + currsize + get_size(next);
            block = previous;
            write_block(block, size, false, get_prev_alloc(block));
            add_to_free(block);

        } else { // prev empty, next occupied
            remove_from_free(previous);
            size_t size = prevsize + currsize;
            block = previous;
            write_block(block, size, false, get_prev_alloc(block));
            add_to_free(block);
        }
    } else {                                    // prev occupied
        if (next != NULL && !get_alloc(next)) { // next empty
            remove_from_free(next);
            size_t size = currsize + get_size(next);
            write_block(block, size, false, prevalloc);
            add_to_free(block);
        } else {
            size_t size = currsize;
            write_block(block, size, false, prevalloc);
            add_to_free(block);
        }
    }
    return block;
}

/**
 * @brief
 *
 * Extends the heap.
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false, get_prev_alloc(block));

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief
 *
 * splits a free block into allocated and free.
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    dbg_requires(asize > 0);

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        write_block(block, asize, true, get_prev_alloc(block));

        block_next = find_next(block);
        write_block(block_next, block_size - asize, false, true);
        add_to_free(block_next);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * searches for a place to fit the newly allocated memory or returns null if
 * none. <What are the function's arguments?> <What is the function's return
 * value?> <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    size_t starter = find_root(asize);

    for (size_t i = starter; i < topval; i++) {
        for (block = seglist[i]; block != NULL; block = block->next) {
            if (asize <= get_size(block)) {
                return block;
            }
        }
    }
    return NULL;
}

// checks to see if a given block is aligned.
bool align_checker(block_t *temp) {
    if (((intptr_t)temp) % 16 != 0) {
        return false;
    }
    return true;
}

// checks to see if a given block is within bounds.
bool bounds_checker(block_t *temp) {
    if ((void *)temp < mem_heap_lo() || (void *)temp < mem_heap_hi()) {
        return false;
    }
    return true;
}

// checks to see if the header and footer are euqal and also that block is of
// valid size.
bool headfoot_checker(block_t *temp) {
    if (temp->header != *(header_to_footer(temp))) {
        return false;
    }
    if (get_size(temp) < min_block_size) {
        return false;
    }
    return true;
}

// checks to see if there are any free spaces that haven't been properly
// coalesced.
bool coalesce_checker(block_t *temp) {
    if (get_alloc(temp) == 0 && get_alloc(find_next(temp)) == 0) {
        return false;
    }
    return true;
}

/**
 * @brief
 *
 * checks various different things to ensure that the heap is valid.
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {

    // check if prologue exist
    block_t *prologue = (block_t *)mem_heap_lo();
    if (!get_alloc(prologue) || get_size(prologue) != 0) {
        printf("No prologue, Line %d\n", line);
        return false;
    }
    // check if epilogue exist
    block_t *epilogue = (block_t *)mem_heap_hi();
    if (!get_alloc(epilogue) || get_size(epilogue) != 0) {
        printf("No epilogue, Line %d\n", line);
        return false;
    }

    // loop thru the heap to check for various things
    block_t *temp = heap_start;
    while (temp != epilogue) {
        if (!align_checker(temp)) {
            printf("Block not aligned, line %d\n", line);
            return false;
        }
        if (!bounds_checker(temp)) {
            printf("Block out of bounds, line %d\n", line);
            return false;
        }
        if (!headfoot_checker(temp)) {
            printf("header/footer wrong, line %d\n", line);
            return false;
        }
        if (!coalesce_checker(temp)) {
            printf("miscoalesced, line %d\n", line);
            return false;
        }
        temp = find_next(temp);
    }
    return true;
}

/**
 * @brief
 *
 * initializes heap and seglist
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    for (size_t i = 0; i < topval; i++) {
        seglist[i] = NULL;
    }

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * creates certain amount of space in memory
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + dsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true, get_prev_alloc(block));
    remove_from_free(block);

    // Try to split the block if too large
    split_block(block, asize);
    block_t *nextb = find_next(block);
    write_block(nextb, get_size(nextb), get_alloc(nextb), true);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false, get_prev_alloc(block));



    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);
    block_t *nextb = find_next(block);
    write_block(nextb, get_size(nextb), get_alloc(nextb), false);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */

