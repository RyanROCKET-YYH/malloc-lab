/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
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
 * @author Yuhong Yao <yuhongy@andrew.cmu.edu>
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
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.
 * Hat tip to Stack Overflow poster chqrlie (see
 * https://stackoverflow.com/questions/72647780).
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__)))
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief define 20 class of seglists*/
const int segclass = 20;

/** @brief define the size of seglist min and max*/
const int segindex_min = 4;
const int segindex_max = 24;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * @brief The size of the initial free block and the default size for expanding
 * the heap. (1 << 12) = 2^12 = 4096 bytes (Must be divisible by dsize) because
 * of alighment
 */
static const size_t chunksize = (1 << 10);

/**
 * @brief Alloc mask is the bit mask tells if the block is being allocated
 * there will be 4 bits in header or footer will be free to use, alloc bit is
 * the last bit
 */
static const word_t alloc_mask = 0x1;

/**
 * @brief prev_alloc mask is the bit mask tells if the previous block is being
 * allocated there will be 4 bits in header or footer will be free to use,
 * bounday tag is the bit left to allocate bit
 */
static const word_t prev_alloc_mask = 0x2;

/**
 * @brief prev_mini mask is the bit mask tells if the previous block is mini
 * block there will be 4 bits in header or footer will be free to use,
 * bounday tag is the bit left to prev_allocate bit
 */
static const word_t prev_mini_mask = 0x4;

/**
 * @brief size mask is used to extract the size of the block from header or
 * footer, since the last four bits are used as flags, size will be the
 * remaining bits
 */
static const word_t size_mask = ~(word_t)0xF;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     *
     * WARNING: A zero-length array must be the last element in a struct, so
     * there should not be any struct fields after it. For this lab, we will
     * allow you to include a zero-length array in a union, as long as the
     * union is the last field in its containing struct. However, this is
     * compiler-specific behavior and should be avoided in general.
     *
     * WARNING: DO NOT cast this pointer to/from other types! Instead, you
     * should use a union to alias this zero-length array with another struct,
     * in order to store additional types of data in the payload memory.
     */
    union {
        struct { // for regular free blocks
            struct block *pred;
            struct block *succ;
        } link_list;
        struct { // for mini blocks
            struct block *next;
        } mini_block;
        char payload[0];
    } body;

    /*
     * Footers would contain the same information as header does. It is not
     * included in the struct because footer will be depand on the payload.
     * Functions such as freeing, coalesing or realloac will take advantage of
     * footer
     */
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/** @brief Pointer to the first block in the free list */
static block_t *free_list_start = NULL;

static block_t **seglist;

// static block_t *mini_block_root = NULL;
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
 * @brief Packs the `size`,`alloc`,`prev_alloc` and `prev_mini` of a block into
 * a word suitable for use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lower 3 bits of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @param[in] prev_alloc True if the prev_block is allocated
 * @param[in] prev_min True if the prev_block is mini block
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool prev_mini) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }

    if (prev_alloc) {
        word |= prev_alloc_mask;
    }

    if (prev_mini) {
        word |= prev_mini_mask;
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
 * @brief Extracts the seg list index according to the size (0-20)
 * @param[in] size the size of block
 * @return The index of seg list
 */
static int get_index(size_t size) {
    int index = segindex_min;

    for (index = segindex_min; index < segindex_max - 1; index++) {
        if (size <= (1 << index)) {
            return (index - segindex_min);
        }
    }
    return (segindex_max - segindex_min - 1);
    // return 1;
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, body.payload));
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
    return (void *)(block->body.payload);
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
    return (word_t *)(block->body.payload + get_size(block) - dsize);
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
    return asize - wsize;
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

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the previous block allocation status of a given header value.
 *
 * This is based on the second lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)(word & prev_alloc_mask);
}

/**
 * @brief Returns the previous allocation status of a block, based on its
 * header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Returns the previous block allocation status of a given header value.
 *
 * This is based on the second lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_prev_mini(word_t word) {
    return (bool)(word & prev_mini_mask);
}

/**
 * @brief Returns the previous allocation status of a block, based on its
 * header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_prev_mini(block_t *block) {
    return extract_prev_mini(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block, bool prev_alloc, bool prev_mini) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true, prev_alloc, prev_mini);
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
 * @pre blocks are inside the heap
 * @post blocks are updated with correct data
 */
// need to make sure the address aligned with dsize
static void write_block(block_t *block, size_t size, bool alloc,
                        bool prev_alloc, bool prev_mini) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    block->header = pack(size, alloc, prev_alloc, prev_mini);
    bool curr_mini = (size == dsize);

    if (!alloc && !curr_mini) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, false, prev_alloc, prev_mini);
    }

    block_t *next_block = find_next(block);
    size_t next_size = get_size(next_block);
    bool next_alloc = get_alloc(next_block);
    next_block->header = pack(next_size, next_alloc, alloc, curr_mini);
}

/**
 * @brief Finds the next free block on the heap.
 *
 * This function accesses the next block in the "explicit list" of the heap
 * by access the succ pointer
 *
 * @param[in] block A block in the heap
 * @return The next free block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next_free(block_t *block) {
    dbg_requires(block != NULL);
    return block->body.link_list.succ;
}

/**
 * @brief Finds the prev free block on the heap.
 *
 * This function accesses the prev free block in the "explicit list" of the heap
 * by access the pred pointer
 *
 * @param[in] block A block in the heap
 * @return The prev free block on the heap
 * @pre The block is not the prologue
 */
static block_t *find_prev_free(block_t *block) {
    dbg_requires(block != NULL);
    return block->body.link_list.pred;
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
    bool prev_mini = get_prev_mini(block);
    if (!prev_mini) {
        word_t *footerp = find_prev_footer(block);

        // Return NULL if called on first block in the heap
        if (extract_size(*footerp) == 0) {
            return NULL;
        }

        return footer_to_header(footerp);
    } else {
        // if prev block is a mini block, just minus the size of mini block
        return (block_t *)((char *)block - dsize);
    }
}

/**
 * @brief Insert a free block into the free list using LIFO policy
 * When the free_list_start is NULL, meaning this block is going to be the first
 * free block when not NULL, the first free list block will has predcessor point
 * to current block.
 * @param[in] block A block being freed in the heap
 * @post update the free list
 */
static void insertFree(block_t *block) {
    // if (get_alloc(block) != 0) {
    //     printf("Insert: Hmmmm... %p\n", (void *) block);
    // }
    size_t size = get_size(block);
    int index = get_index(size);
    // printf("496, size: %lu, %d\n", size, index);
    if (size == dsize) { // manage mini_block free list
        block->body.mini_block.next = seglist[0];
        // printf("577 next free in mini_block %p\n", (void *) block->body.mini_block.next);
    } else {
        block->body.link_list.pred = NULL;
        // printf("%p, %p\n", (void *) block, (void *) seglist[index]);
        block->body.link_list.succ = seglist[index];
        if (seglist[index] != NULL) {
            seglist[index]->body.link_list.pred = block;
        }
    }
    seglist[index] = block;
}

/**
 * @brief the side effect of a block being allocated.
 * remove block from the free list, Following LIFO policy.
 *
 * @param[in] block A block being allocated in the heap
 */
static void removeFree(block_t *block) {
    size_t size = get_size(block);
    int index = get_index(size);

    if (size == dsize) { // if it is in the mini_block free list
        block_t *curr = seglist[0];
        block_t *prev = NULL; // set a prev pointer as a local

        while (curr != NULL) { // traverse through mini_block free list because
                               // there is no prev
            if (curr == block) {
                if (prev == NULL) { // first in the free block
                    seglist[0] = curr->body.mini_block.next;
                } else { // except the first block situation
                    prev->body.mini_block.next = curr->body.mini_block.next;
                }
                break;
            }
            prev = curr;
            curr = curr->body.mini_block.next;
        }

    } else { // free block size that are bigger than dsize
        block_t *pred = block->body.link_list.pred;
        block_t *succ = block->body.link_list.succ;

        // only free block
        if (pred == NULL && succ == NULL) {
            seglist[index] = NULL;
        }
        // first free block
        else if (pred == NULL && succ != NULL) {
            seglist[index] = succ;
            succ->body.link_list.pred = NULL;
        }
        // middle free block
        else if (pred != NULL && succ != NULL) {
            pred->body.link_list.succ = succ;
            succ->body.link_list.pred = pred;
        }
        // last free block
        else if (pred != NULL && succ == NULL) {
            pred->body.link_list.succ = NULL;
        }
    }
}

static void print_heap(void) {
    block_t *block = heap_start;
    printf("--------------------------\n");
    printf("Heap START\n");
    while (get_size(block) != 0) {
        size_t size = get_size(block);
        bool allocated = get_alloc(block);
        bool prev_alloc = get_prev_alloc(block);
        bool prev_mini = get_prev_mini(block);
        bool curr_mini = (size == dsize) ? true : false;

        printf("Block %p, size %lu, allocated %d, prev_allocated %d, prev_mini "
               "%d, header %lx\n",
               (void *)block, size, allocated, prev_alloc, prev_mini,
               block->header);

        if (!allocated) {
            int index = get_index(size);
            block_t *free_block = seglist[index];
            printf("Free block in seglist[%d], block %p\n", index,
                   (void *)free_block);
            if (!curr_mini) {
                word_t *footerp = header_to_footer(block);
                block_t *pred = block->body.link_list.pred;
                block_t *succ = block->body.link_list.succ;
                printf("Footer: %lx\n", *footerp);
                printf("prev free block %p, next free block %p\n", (void *)pred,
                       (void *)succ);
            } else {
                block_t *next = block->body.mini_block.next;
                printf("next free block %p\n", (void *)next);
            }
        }
        block = find_next(block);
    }
    printf("Heap END\n");
    printf("--------------------------\n");
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief Coalesce block based on 4 cases
 * case 1: prev and next are allocated
 * case 2: only next is free
 * case 3: only prev is free
 * case 4: both prev and next are free
 *
 * @param[in] block A pointer to the block need to coalesce
 * @return A pointer to the beginning of the free block
 */
static block_t *coalesce_block(block_t *block) {
    /* get the previous and next block size and allocate info */
    block_t *next_block = find_next(block);
    bool prev_alloc = get_prev_alloc(block);
    bool next_alloc = (next_block == NULL) ? true : get_alloc(next_block);
    size_t size = get_size(block);
    bool prev_mini = get_prev_mini(block);

    if (!get_alloc(block)) {
        if (prev_alloc && next_alloc) { /* Case 1 */
            // write_block(block, size, false);
        } else if (prev_alloc && !next_alloc) { /* Case 2 */
            size += get_size(next_block);
            removeFree(next_block);
            write_block(block, size, false, prev_alloc, prev_mini);
        } else if (!prev_alloc && next_alloc) { /* Case 3 */
            block_t *prev_block = find_prev(block);
            prev_mini = get_prev_mini(prev_block);
            removeFree(prev_block);
            size += get_size(prev_block);
            block = prev_block;
            write_block(block, size, false, true, prev_mini);
        } else if (!prev_alloc && !next_alloc) { /* Case 4 */
            block_t *prev_block = find_prev(block);
            prev_mini = get_prev_mini(prev_block);
            removeFree(prev_block);
            removeFree(next_block);
            size += get_size(prev_block) + get_size(next_block);
            block = prev_block;
            write_block(block, size, false, true, prev_mini);
        }
        insertFree(block);
    }
    return block;
}

/**
 * @brief Used to extend heap by specified amount.
 *
 * @param[in] size The size that heap should be extend
 * @return A pointer to the start of the block that is extended
 * @pre size need to be greater than 0
 * @post The heap is extended by at least size bytes.(round up to even number of
 * words)
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    /*
     * bp is the new block payload, write the new block starting one word before
     * bp is because we need to write the head for the block then precedes with
     * payload. (done by payload_to_header) the block will still have total size
     * of header+payload+footer that we requested. And because we have old
     * epilogue, so we can use one word before bp to replace with our new
     * header, and write a new epilogue after and wouldn't affect the heap
     */

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    bool prev_alloc = get_prev_alloc(block);
    bool prev_mini = get_prev_mini(block);
    write_block(block, size, false, prev_alloc, prev_mini);
    bool curr_mini = (size == dsize) ? true : false;

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next, false, curr_mini);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief This funciton splits a block into two blocks.
 * one with the size of requested asize, and the other is the size of block
 * initial size - asize, (this size has to be greater than min_block_size) The
 * first block will be allocated, and the second is free
 *
 * @param[in] block A pointer to the block that need to be splited
 * @param[in] asize The size of the first block we want to split
 * @pre The block has to be allocted and asize need to be greater than block
 * size
 * @post The block still need to be allocated.
 */
static void split_block(block_t *block, size_t asize, size_t block_size) {
    dbg_requires(get_alloc(block));
    /* TODO: Can you write a precondition about the value of asize? */

    // size_t block_size = get_size(block);
    if ((block_size - asize) >= min_block_size) {
        block_t *block_next;
        bool prev_mini = get_prev_mini(block);
        write_block(block, asize, true, true, prev_mini);
        block_next = find_next(block);
        bool curr_mini = (asize == dsize) ? true : false;
        write_block(block_next, block_size - asize, false, true, curr_mini);
        // insert the new free block into the list
        insertFree(block_next);
        // coalesce_block(block_next);
    }
    dbg_ensures(get_alloc(block));
}

/**
 * @brief Search for the availbe block on heap using first fit.
 *
 * @param[in] asize The size of the block need to be allocated.
 * @return The pointer to the first fitted block. If no fit return NULL.
 * @pre It assumes that the heap is initialized and asize is valid.
 * @post The block that returned is free and large enough to allocate.
 */
static block_t *find_fit(size_t asize) {
    block_t *block;
    int start_index = (asize <= dsize) ? 0 : get_index(asize);

    // if (asize == dsize) {
    //     block = seglist[0];
    //     while (block != NULL) {
    //         if (!(get_alloc(block)) && (asize <= get_size(block))) {
    //             return block;
    //         }
    //         block = block->body.mini_block.next;
    //     }
    // }

    // printf("Called get_index with size: %lu\n", asize);
    for (int index = start_index; index < segclass; index++) {
        // printf("Called get_index with size: %lu, size threshold: %lu\n",
        // asize, (size_t)(1 << (index+4))); dbg_printf("Current block: %p,
        // Succ: %p\n", (void*)block, (void*)block->body.link_list.succ);
        block = seglist[index];
        // printf("Returning index %d, block %p\n", index, (void *) block);
        while (block != NULL) {
            if (!(get_alloc(block)) && (asize <= get_size(block))) {
                return block;
            }
            
            if (index == 0) {
                block = block->body.mini_block.next;
            } else {
                block = block->body.link_list.succ;
            }
        }
    }
    return NULL; // no fit found
}

/**
 * @brief Search for the availbe block on heap using best fit.
 *
 * @param[in] asize The size of the block need to be allocated.
 * @return The pointer to the first fitted block. If no fit return NULL.
 * @pre It assumes that the heap is initialized and asize is valid.
 * @post The block that returned is free and large enough to allocate.
 */
static block_t *best_fit(size_t asize) {
    block_t *block;
    block_t *best_block = NULL;
    size_t diff = 0;

    for (block = free_list_start; block != NULL;
         block = find_next_free(block)) {
        if (!(get_alloc(block)) && (asize <= get_size(block))) {
            if (diff == 0 || diff > get_size(block)) {
                diff = get_size(block);
                best_block = block;
            }
        }
    }
    return best_block;
}

/**
 * @brief Heap checker
 * Able to check the prologue and epilogue,check block lies within heap boundary
 * address alignment, header and footer match each other, coalescing, next and
 * previous pointers are consistent, all seg free blocks falls within size range
 * of bucket lists, free blocks match each other in heap and free list
 *
 * @param[in] line line number causing the fault
 * @return true or false based on heap condition
 */
bool mm_checkheap(int line) {
    block_t *block;
    word_t *prologue = (word_t *)heap_start - 1;
    int free_count_heap = 0;
    int free_count_list = 0;
    // check prologue
    if (*prologue != pack(0, true, true, false)) {
        dbg_printf("Error with prologue blocks.");
        return false;
    }

    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {
        if ((size_t)header_to_payload(block) %
            dsize) { /* check block alignment is a multiple of 16*/
            dbg_printf("Block at %p is not aligned at line %d\n", (void *)block,
                       line);
            return false;
        }

        if (get_size(block) <
            min_block_size) { /* check block's size is greater than minimum */
            dbg_printf("Block size error at %p, at line %d\n", (void *)block,
                       line);
            return false;
        }

        if (!get_alloc(block) && !(get_size(block) == dsize)) {
            // check each block's header and footer
            if (get_alloc(block) != extract_alloc(*header_to_footer(block)) ||
                get_size(block) != extract_size(*header_to_footer(block)) ||
                get_prev_alloc(block) !=
                    extract_prev_alloc(*header_to_footer(block))) {
                dbg_printf(
                    "Header and footer does not match with each other at "
                    "%p, at line %d\n",
                    (void *)block, line);
                return false;
            }
        }

        // check prev_alloc_bit matches
        if (get_alloc(block) != get_prev_alloc(find_next(block))) {
            dbg_printf("Previous allocation bit does not match at line %d\n",
                       line);
            return false;
        }

        if (get_alloc(block)) {
            // check prev_mini_bit matches
            if ((get_size(block) == dsize) != get_prev_mini(find_next(block))) {
                dbg_printf("Previous mini bit does not match at line %d\n",
                           line);
                return false;
            }
        }

        // check blocks lie within heap boundaries
        if ((void *)block < mem_heap_lo() || (void *)block > mem_heap_hi()) {
            dbg_printf("Block at %p is outside heap.\n", (void *)block);
            return false;
        }

        // check coalescing
        if (!get_alloc(block) && !get_alloc(find_next(block))) {
            dbg_printf("Consecutive free blocks in the heap at line %d\n",
                       line);
            return false;
        }

        // get free blocks counts on heap
        if (!get_alloc(block)) {
            free_count_heap += 1;
        }
    }

    // check epilogue
    if (!get_alloc(block) || get_size(block) != 0) {
        dbg_printf("Error with epilogue blocks.");
        return false;
    }

    for (int i = 0; i < segclass; i++) {
        block_t *current_block = seglist[i];

        while (current_block != NULL) {
            // check all free lists are inside heap boundaries
            if ((void *)current_block < mem_heap_lo() ||
                (void *)current_block > mem_heap_hi()) {
                dbg_printf("Block at %p is outside heap boundaries at line %d\n",
                           (void *)current_block, line);
                return false;
            }
            // check all blocks in free list are free
            if (get_alloc(current_block)) {
                dbg_printf("Allocated block in the free list\n");
                return false;
            }
            // check all blocks fall within bucket size range
            size_t size = get_size(current_block);
            int index = get_index(size);
            if (index != i) {
                dbg_printf("Block at %p not within bucket size range\n",
                           (void *)current_block);
                return false;
            }

            if (i == 0) {
                block_t *next_free_mini = current_block->body.mini_block.next;
                if (next_free_mini != NULL &&
                    ((void *)next_free_mini < mem_heap_lo() ||
                     (void *)next_free_mini > mem_heap_hi())) {
                    dbg_printf(
                        "Next mini block at %p is outside heap boundaries\n",
                        (void *)next_free_mini);
                    return false;
                }
                current_block = next_free_mini;
            } else {
                // check consistency
                block_t *next_free = current_block->body.link_list.succ;
                block_t *prev_free = current_block->body.link_list.pred;
                // if a's next point to b, b's prev should point to a
                if (next_free != NULL &&
                    next_free->body.link_list.pred != current_block) {
                    dbg_printf("Next/previous pointers are not consistent at "
                               "line %d\n",
                               line);
                    return false;
                }

                if (prev_free != NULL &&
                    prev_free->body.link_list.succ != current_block) {
                    dbg_printf("Next/previous pointers are not consistent at "
                               "line %d\n",
                               line);
                    return false;
                }
                current_block = next_free;
            }
            free_count_list += 1;
        }
    }

    if (free_count_heap != free_count_list) {
        dbg_printf(
            "Free block count on heap does not match with explicit free lists");
        // printf("free_count_heap %d, free_count_list
        // %d\n",free_count_heap,free_count_list);
        return false;
    }

    return true;
}

/**
 * @brief Create an initial heap and extend heap with a free block of chunksize
 * bytes
 *
 * <What are the function's arguments?> No Arguments
 * @return whether the heap is successfully initialized.
 * @post the heap will initialized with prologue and epilogue
 */
bool mm_init(void) {
    size_t seglist_space = segclass * sizeof(block_t *);
    size_t initial_space = seglist_space + 2 * wsize;

    // Create the initial empty heap with seglist pointers, prologue and
    // epilogue
    word_t *start = (word_t *)(mem_sbrk((intptr_t)initial_space));
    if (start == (void *)-1) {
        return false;
    }
    /*
     * Heap prologue marks the beginning of the heap, and epilogue marks the end
     * of the heap. Prologue correspond to footer and epilogue correspond to
     * header are preventing them from coalescing operation.
     */
    seglist = (block_t **)(start);
    for (int i = 0; i < segclass; i++) {
        seglist[i] = NULL;
    }
    start[segclass] =
        pack(0, true, true, false); // Heap prologue (block footer)
    start[segclass + 1] =
        pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1 + segclass]);
    // Extend the empty heap with a free block of chunksize bytes
    block_t *initial_block = extend_heap(chunksize);
    if (initial_block == NULL) {
        return false;
    }
    // free_list_start = NULL;
    return true;
}

/**
 * @brief Dynamically allocating a block of memory of a specified size.
 *
 * @param[in] size The requested size of memory to be allocated.
 * @return A pointer to the allocated block payload, NULL if failed malloc.
 * @pre Need to checkheap, ensure no errors on heap.
 * @post Need to checkheap again after malloc
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;
    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }
    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }
    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // if (asize == dsize) {
    //     asize = round_up(size + dsize, dsize);
    // }

    // printf("current allocation size %lu, round-up size %lu\n", size, asize);
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
    // Remove block from free list
    removeFree(block);
    bool prev_mini = get_prev_mini(block);
    write_block(block, block_size, true, true, prev_mini);
    // Try to split the block if too large
    split_block(block, asize, block_size);
    bp = header_to_payload(block);
    dbg_ensures(mm_checkheap(__LINE__));
    // print_heap();
    return bp;
}

/**
 * @brief Deallocate the memroy blocks from heap
 *
 * @param[in] bp The pointer to block payload that need to be deallocated
 * @pre need to pass heap checker, the block is allocated before free
 * @post set the block to free, coalesce with neighbors and pass heap checker
 * again.
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
    bool prev_alloc = get_prev_alloc(block);
    bool prev_mini = get_prev_mini(block);
    // Mark the block as free
    write_block(block, size, false, prev_alloc, prev_mini);
    // printf("block address after being freed %p\n", (void *)block);
    // Try to coalesce the block with its neighbors
    coalesce_block(block);
    // print_heap();
    dbg_ensures(mm_checkheap(__LINE__));
    // if (!mm_checkheap(__LINE__)) {
    //     dbg_printf("Assertion\n");
    //     assert(0);
    // }
}

/**
 * @brief reallocate memory block pointed to the newptr of size bytes
 *
 * @param[in] ptr A pointer to the block that need to be reallocated
 * @param[in] size the new size of the block
 * @return A pointer to the new allocated memory block
 * @post the old block will be freed and is being copied to the new block.
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
 * @brief Similar to malloc, but set all bits to zero after malloc.
 *
 * @param[in] elements The number of elements need to be allocated.
 * @param[in] size The size of each element
 * @return A pointer to the allocated memory
 * @post The allocated memory is initialized to zero.
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
