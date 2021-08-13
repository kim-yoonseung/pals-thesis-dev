#pragma once

#include "main.h"
#include <stdint.h>

#ifndef FOR_TESTING

/* config */
extern const uint64_t PALS_PERIOD;
extern const uint64_t MAX_CSKEW;
extern const uint64_t MAX_NWDELAY;

extern const int MSG_SIZE;
extern const int NUM_TASKS;
extern const int NUM_MCASTS;

extern const int PORT;
extern const char IP_ADDR[_MAX_NUM_TASKS + _MAX_NUM_MCASTS][_IP_LENGTH];
extern const char MCAST_MEMBER[_MAX_NUM_MCASTS][_MAX_NUM_TASKS];

extern const char TASK_ID;

void job(uint64_t pbt, inbox_t *inbox);

#endif
