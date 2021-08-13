.PHONY: all

LIB_DIR = ../build
INCLUDE_DIR = ../include

SRC_FILES = timer_simple.c send_abc.c recv.c recv_mcast.c

OBJS = $(addprefix $(LIB_DIR)/, $(SRC_FILES:.c=))

all: $(OBJS)

$(LIB_DIR)/%: %.c $(LIB_DIR)/libpals.so
	gcc -I$(INCLUDE_DIR) -L$(LIB_DIR) -o $@ $< -lpals
