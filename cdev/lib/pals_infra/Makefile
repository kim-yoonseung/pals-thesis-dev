.PHONY: all tests

BUILD_DIR=build
INCLUDE_DIR=include
SRC_DIR=src

all: $(BUILD_DIR)/libpals.so

$(BUILD_DIR)/libpals.so: $(SRC_DIR)/pals_infra.c $(INCLUDE_DIR)/pals_infra.h
	mkdir -p $(BUILD_DIR)
	gcc -Iinclude -shared -o $@ -fPIC $<

tests:
	make -C tests

clean:
	rm -rf $(BUILD_DIR)
