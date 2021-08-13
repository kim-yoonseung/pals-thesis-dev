#include "app.h"
#include <stdint.h>

const uint64_t PALS_PERIOD = 260000000;
const uint64_t MAX_CSKEW   =  20000000;
const uint64_t MAX_NWDELAY =  12000000;

const int NUM_TASKS = 7;
const int NUM_MCASTS = 3;
const int MSG_SIZE = 11;

const int PORT = 41000;
const char IP_ADDR[_MAX_NUM_TASKS + _MAX_NUM_MCASTS][_IP_LENGTH] =
  { "192.168.1.1",
    "192.168.2.1",
    "192.168.3.3",
    "192.168.4.4",
    "192.168.5.5",
    "192.168.6.6",
    "192.168.7.7",
    "226.1.0.0",
    "230.0.1.0",
    "231.0.0.1",
  };

const char MCAST_MEMBER[_MAX_NUM_MCASTS][_MAX_NUM_TASKS] =
  {
    { 0, 0, 0, 0, 0, 0, 1 },
    { 1, 0, 0, 1, 0, 0, 0 },
    { 0, 1, 0, 0, 1, 0, 1 },
  };
