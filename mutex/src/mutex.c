#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>
#include <stdbool.h>

#define NUM_THREADS 3
#define NUM_ITERATIONS 5

// Shared mutex and condition variables
pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t turn = PTHREAD_COND_INITIALIZER;

// Queue implementation
typedef struct QueueNode {
    int thread_id;
    struct QueueNode* next;
} QueueNode;

QueueNode* queue_head = NULL;
QueueNode* queue_tail = NULL;
pthread_mutex_t queue_lock = PTHREAD_MUTEX_INITIALIZER;

// Queue operations
void enqueue(int thread_id) {
    QueueNode* node = malloc(sizeof(QueueNode));
    node->thread_id = thread_id;
    node->next = NULL;
    
    pthread_mutex_lock(&queue_lock);
    if (queue_tail == NULL) {
        queue_head = queue_tail = node;
    } else {
        queue_tail->next = node;
        queue_tail = node;
    }
    pthread_mutex_unlock(&queue_lock);
}

int dequeue() {
    pthread_mutex_lock(&queue_lock);
    if (queue_head == NULL) {
        pthread_mutex_unlock(&queue_lock);
        return -1;
    }
    
    QueueNode* node = queue_head;
    int thread_id = node->thread_id;
    queue_head = node->next;
    if (queue_head == NULL) queue_tail = NULL;
    
    free(node);
    pthread_mutex_unlock(&queue_lock);
    return thread_id;
}

bool is_next_in_queue(int thread_id) {
    pthread_mutex_lock(&queue_lock);
    bool result = (queue_head != NULL && queue_head->thread_id == thread_id);
    pthread_mutex_unlock(&queue_lock);
    return result;
}

// Thread states for visualization
typedef enum {
    NONCRITICAL,
    TRYING,
    CRITICAL
} State;

// Thread state array for visualization
State thread_states[NUM_THREADS];
pthread_mutex_t state_lock = PTHREAD_MUTEX_INITIALIZER;

void print_states() {
    const char* state_strings[] = {"NONCRIT", "TRYING ", "CRITICAL"};
    printf("\r");
    for (int i = 0; i < NUM_THREADS; i++) {
        printf("Thread %d: %s | ", i, state_strings[thread_states[i]]);
    }
    fflush(stdout);
}

void set_state(int thread_id, State new_state) {
    pthread_mutex_lock(&state_lock);
    thread_states[thread_id] = new_state;
    print_states();
    pthread_mutex_unlock(&state_lock);
}

void* thread_function(void* arg) {
    int thread_id = *(int*)arg;
    
    for (int i = 0; i < NUM_ITERATIONS; i++) {
        // Non-critical section
        set_state(thread_id, NONCRITICAL);
        usleep(rand() % 1000000);  // Random sleep up to 1 second
        
        // Try to enter critical section
        set_state(thread_id, TRYING);
        enqueue(thread_id);  // Add to waiting queue
        
        pthread_mutex_lock(&lock);
        // Wait until we're at the head of the queue
        while (!is_next_in_queue(thread_id)) {
            pthread_cond_wait(&turn, &lock);
        }
        
        // Critical section
        set_state(thread_id, CRITICAL);
        usleep(rand() % 1000000);  // Random sleep up to 1 second
        
        // Exit critical section
        dequeue();  // Remove from queue
        pthread_mutex_unlock(&lock);
        pthread_cond_broadcast(&turn);  // Signal other waiting threads
    }
    
    free(arg);
    return NULL;
}

int main() {
    pthread_t threads[NUM_THREADS];
    
    // Initialize random seed
    srand(time(NULL));
    
    printf("Mutex Lock Demonstration\n");
    printf("Each thread will attempt to enter critical section %d times\n\n", NUM_ITERATIONS);
    
    // Create threads
    for (int i = 0; i < NUM_THREADS; i++) {
        int* thread_id = malloc(sizeof(int));
        *thread_id = i;
        thread_states[i] = NONCRITICAL;
        pthread_create(&threads[i], NULL, thread_function, thread_id);
    }
    
    // Wait for all threads to complete
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }
    
    printf("\n\nAll threads completed successfully!\n");
    
    // Cleanup
    pthread_mutex_destroy(&lock);
    pthread_mutex_destroy(&state_lock);
    
    return 0;
}
