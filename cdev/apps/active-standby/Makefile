.PHONY: all exec testobj clight clean

LIB_INF_DIR=../../lib/pals_infra/build
LIB_INF_INCLUDE_DIR=../../lib/pals_infra/include

LIB_MW_DIR=../../build
LIB_MW_INCLUDE_DIR=../../src

BUILD_DIR=build
INCLUDE_DIR=src
SRC_DIR=src

CLIGHTGEN=clightgen

SRC_FILES = system.c config.c test_config.c console.c ctrl.c dev.c
EXEC_FILES = console ctrl1 ctrl2 dev1 dev2 dev3
VERIF_FILES = config.v config2.v console.v ctrl.v dev.v
TEST_FILES = test_config.o $(addsuffix _test.o, $(EXEC_FILES))

SRCS = $(addprefix $(SRC_DIR)/, $(SRC_FILES))
OBJS = $(addprefix $(BUILD_DIR)/, $(SRC_FILES:.c=.o))
EXECS = $(addprefix $(BUILD_DIR)/, $(EXEC_FILES))
VERIFS = $(addprefix $(BUILD_DIR)/, $(VERIF_FILES))
TESTS = $(addprefix $(BUILD_DIR)/, $(TEST_FILES))

CC = gcc
CFLAGS =
INCLUDE = -I$(LIB_INF_INCLUDE_DIR) -I$(LIB_MW_INCLUDE_DIR) -I$(INCLUDE_DIR)

all: exec testobj clight

exec: $(BUILD_DIR) $(EXECS)

testobj: $(BUILD_DIR) $(TESTS)

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/config.o: $(SRC_DIR)/config.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ $<

$(BUILD_DIR)/test_config.o: $(SRC_DIR)/test_config.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ $<

$(BUILD_DIR)/console.o: $(SRC_DIR)/console.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ -D_TASK_ID=0 $<

$(BUILD_DIR)/console_test.o: $(SRC_DIR)/console.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ -DFOR_TESTING -D_TASK_ID=0 $<


$(BUILD_DIR)/ctrl%.o: $(SRC_DIR)/ctrl.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ -D_TASK_ID=$* $<

$(BUILD_DIR)/ctrl%_test.o: $(SRC_DIR)/ctrl.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ -DFOR_TESTING -D_TASK_ID=$* $<

$(BUILD_DIR)/dev%.o: $(SRC_DIR)/dev.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ -D_TASK_ID=$$(($* + 2)) $<

$(BUILD_DIR)/dev%_test.o: $(SRC_DIR)/dev.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ -DFOR_TESTING -D_TASK_ID=$$(($* + 2)) $<


$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c
	$(CC) $(CFLAGS) $(INCLUDE) -c -o $@ $<

$(BUILD_DIR)/%: $(BUILD_DIR)/%.o $(BUILD_DIR)/system.o $(BUILD_DIR)/config.o
	$(CC) -o $@ -L$(LIB_INF_DIR) $^ $(LIB_MW_DIR)/main.o -lpals

$(BUILD_DIR)/%.v: $(SRC_DIR)/%.c
	$(CLIGHTGEN) $(INCLUDE) $^
	mv $(SRC_DIR)/$*.v $(BUILD_DIR)/

clight: $(VERIFS)

clean:
	rm -rf $(BUILD_DIR)
