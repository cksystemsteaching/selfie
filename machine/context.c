#include <stddef.h>

#include "context.h"
#include "config.h"
#include "tinycstd.h"

struct context kernel_context;

uint64_t num_of_used_contexts = 0;
struct context_manager* currently_active_context;

struct context_manager {
    struct context context;
    char is_used;
    struct context_manager* prev_scheduled;
    struct context_manager* next_scheduled;
};

struct context_manager all_contexts[MAX_AMOUNT_OF_CONTEXTS];

struct context* kallocate_context() {
    struct context_manager* context_manager;
    struct context_manager* prev_scheduled = &all_contexts[0];
    struct context_manager* next_scheduled = &all_contexts[0];

    if (num_of_used_contexts == MAX_AMOUNT_OF_CONTEXTS)
        return NULL;

    for (size_t i = 0; i < MAX_AMOUNT_OF_CONTEXTS; ++i) {
        context_manager = &all_contexts[i];

        if (!context_manager->is_used) {
            context_manager->is_used = 1;
            ++num_of_used_contexts;
            context_manager->context.id = i + 1; // id 0 is reserved for the kernel context
            
            context_manager->prev_scheduled = prev_scheduled;
            context_manager->next_scheduled = next_scheduled;
            prev_scheduled->next_scheduled = context_manager;
            next_scheduled->prev_scheduled = context_manager;

            return &context_manager->context;
        } else {
            prev_scheduled = context_manager;
            next_scheduled = context_manager->next_scheduled;
        }
    }

    return NULL; // acutally unreachable but the compiler is too dumb to see this
}

extern void _start_hang();

void kfree_context(uint64_t context_id) {
    struct context_manager* context_manager = &all_contexts[context_id - 1];

    context_manager->is_used = 0;
    --num_of_used_contexts;

    if (num_of_used_contexts == 0) {
        printf("KERNEL PANIC: all processes are dead. starting to hang...\n");
        _start_hang(); // TODO: maybe change something here
    }

    context_manager->prev_scheduled->next_scheduled = context_manager->next_scheduled;
    context_manager->next_scheduled->prev_scheduled = context_manager->prev_scheduled;
}

struct context* get_currently_active_context() {
    return &currently_active_context->context;
}

struct context* schedule_next_context() {
    currently_active_context = currently_active_context->next_scheduled;

    return &currently_active_context->context;
}
