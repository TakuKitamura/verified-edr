#include <stdio.h>
#include <pthread.h>
#include <unistd.h>
#include <stdlib.h>

#include "request.h"
#include "syncchannel.h"
#include "request_manager.h"
#include "debug.h"
#include "random.h"
#include "tracemanager.h"

/* Main mutex */
pthread_mutex_t __mainMutex;

/* Synchronous channels */
/* Asynchronous channels */

#include "EDRSystemBlock.h"


int main(int argc, char *argv[]) {
  
  /* disable buffering on stdout */
  setvbuf(stdout, NULL, _IONBF, 0);
  
  /* Synchronous channels */
  /* Asynchronous channels */
  
  /* Threads of tasks */
  pthread_t thread__EDRSystemBlock;
  /* Activating tracing  */
  /* Activating randomness */
  initRandom();
  /* Initializing the main mutex */
if (pthread_mutex_init(&__mainMutex, NULL) < 0) { exit(-1);}
  
  /* Initializing mutex of messages */
  initMessages();
  
  
  pthread_create(&thread__EDRSystemBlock, NULL, mainFunc__EDRSystemBlock, (void *)"EDRSystemBlock");
  
  
  pthread_join(thread__EDRSystemBlock, NULL);
  
  
  return 0;
  
}
