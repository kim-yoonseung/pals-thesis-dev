#pragma once

#include <stdint.h>

/** MSG_SIZE */
/*   Set to (8k + 7) bytes in order to maximize utilization, */
/*  considering the alignment  */
#ifndef _MSG_SIZE_K
#define _MSG_SIZE_K 1
#endif

#ifndef _MAX_NUM_TASKS
#define _MAX_NUM_TASKS 16
#endif

#ifndef _MAX_NUM_MCASTS
#define _MAX_NUM_MCASTS 8
#endif

/* #define _MSG_SIZE_K 2 */
#define _MAX_MSG_SIZE (8 * _MSG_SIZE_K + 7)

#define _IP_LENGTH 16

#define CONCAT_NAMES(pref, TID) pref##_##TID

#ifdef FOR_TESTING
#define TEST_STATIC static
#define JOB_FNAME(TID) CONCAT_NAMES(job, TID)
#else
#define TEST_STATIC
#define JOB_FNAME(TID) job
#endif

#define INIT_FNAME(TID) CONCAT_NAMES(init, TID)

/** System constants (parametric in verification) */

/* #define _MAX_NUM_TASKS 7 */
/* #define _MAX_NUM_MCASTS 5 */

/* #define _PALS_PERIOD 100000000 */
/* #define _MAX_CSKEW 5000000 */
/* #define _MAX_NWDELAY 5000000 */
/* #define _PORT 33333 */

/* #define _IP_ADDR				\ */
/*   {						\ */
/*     "192.168.1.1",				\ */
/*     "192.168.2.1",				\ */
/*     "192.168.2.2",				\ */
/*     "192.168.3.1",				\ */
/*     "192.168.3.2",				\ */
/*     "192.168.3.3",				\ */
/*     "238.0.0.1",				\ */
/*   } */

/* #define _MCAST_MEMBER				\ */
/*   {						\ */
/*     { 0, 1, 1, 0, 0, 0 },			\ */
/*   } */

// 0.1 sec = 100 ms

/* #define NUM_MCAST_GROUPS 1 */


/* #define ID_CON 0 */
/* #define ID_CTRL1 1 */
/* #define ID_CTRL2 2 */
/* #define ID_DEV1 3 */
/* #define ID_DEV2 4 */
/* #define ID_DEV3 5 */
/* #define ID_MCAST 6 */

/* #define OWNER_TIMEOUT 5 */
/* #define NUM_DEVICES 3 */

typedef struct msg_entry_t {
  char received;
  char content[_MAX_MSG_SIZE];
} msg_entry_t;

typedef struct inbox_t {
  msg_entry_t entry[_MAX_NUM_TASKS];
} inbox_t;


/* // TODO: change */
/* extern const char IP_ADDR[][_IP_LENGTH]; */

void pals_send(char tid, char *msg);
