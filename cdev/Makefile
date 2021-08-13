.PHONY: all objs clight clean apps apps-clean

LIB_DIR=lib/pals_infra/build
LIB_INCLUDE_DIR=lib/pals_infra/include

BUILD_DIR=build
INCLUDE_DIR=src
SRC_DIR=src

CLIGHTGEN=clightgen

HEADER_FILES = main.h app.h
SRC_FILES = main.c test_interface_impl.c
VERIF_FILES = main1.v main2.v

HEADERS = $(addprefix $(SRC_DIR)/, $(HEADER_FILES))
SRCS = $(addprefix $(SRC_DIR)/, $(SRC_FILES))
OBJS = $(addprefix $(BUILD_DIR)/, $(SRC_FILES:.c=.o))
VERIFS = $(addprefix $(BUILD_DIR)/, $(VERIF_FILES))

CC = gcc
CFLAGS =
INCLUDE = -I$(LIB_INCLUDE_DIR) -I$(INCLUDE_DIR)


objs: $(BUILD_DIR) $(OBJS)

all: objs clight apps

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/test_interface_impl.o: $(SRC_DIR)/test_interface_impl.c $(HEADERS) $(SRC_DIR)/test_interface.h
	ocamlopt -c $<
	mv test_interface_impl.o $@

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c $(HEADERS)
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ $<

#$(BUILD_DIR)/main2.o: $(SRC_DIR)/main.c $(HEADERS)
#	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ $< -D_MSG_SIZE_K=2 -D_MAX_NUM_TASKS=7 -D_MAX_NUM_MCASTS=5

$(BUILD_DIR)/main1.v: $(SRC_DIR)/main.c $(HEADERS)
	$(CLIGHTGEN) $(INCLUDE) $< -o $@

$(BUILD_DIR)/main2.v: $(SRC_DIR)/main.c $(HEADERS)
	$(CLIGHTGEN) $(INCLUDE) $< -o $@ -D_MSG_SIZE_K=2 -D_MAX_NUM_TASKS=13 -D_MAX_NUM_MCASTS=15


#$(BUILD_DIR)/%.v: $(SRC_DIR)/%.c $(HEADERS)
#	$(CLIGHTGEN) $(INCLUDE) $<
#	mv $(SRC_DIR)/$*.v $(BUILD_DIR)/

clight: $(VERIFS)
# 	$(CLIGHTGEN) $(INCLUDE) $^
# 	mv $(SRC_DIR)/*.v $(BUILD_DIR)/

clean: apps-clean
	rm -rf $(BUILD_DIR)


apps:
	make -C apps/active-standby all

apps-clean:
	make -C apps/active-standby clean
