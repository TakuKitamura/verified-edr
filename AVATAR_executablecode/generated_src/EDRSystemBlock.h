#ifndef EDRSystemBlock_H
#define EDRSystemBlock_H
#include <stdio.h>
#include <pthread.h>
#include <unistd.h>
#include <stdlib.h>

#include "request.h"
#include "syncchannel.h"
#include "request_manager.h"
#include "debug.h"
#include "defs.h"
#include "mytimelib.h"
#include "random.h"
#include "tracemanager.h"
#include "main.h"

extern void *mainFunc__EDRSystemBlock(void *arg);
__attribute__((unused)) request __req0__EDRSystemBlock;
__attribute__((unused))int *__params0__EDRSystemBlock[0];
__attribute__((unused)) request __req1__EDRSystemBlock;
__attribute__((unused))int *__params1__EDRSystemBlock[0];
__attribute__((unused)) request __req2__EDRSystemBlock;
__attribute__((unused))int *__params2__EDRSystemBlock[0];
__attribute__((unused))setOfRequests __list__EDRSystemBlock;
__attribute__((unused))pthread_cond_t __myCond__EDRSystemBlock;
__attribute__((unused))request *__returnRequest__EDRSystemBlock;

#endif
