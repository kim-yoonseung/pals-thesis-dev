.PHONY: all clean

all:
	mkdir -p build
	cp ../../cdev/build/test_interface_impl.o build/
	cp ../../cdev/apps/active-standby/build/test_config.o build/
	cp ../../cdev/apps/active-standby/build/*_test.o build/
	cp ../generic/Generic.mli build/AppSystem.mli
	cp ../generic/Generic.ml build/AppSystem.ml
	cp Driver.ml build/
	cp ../common/TestInterface.ml build/
	cp ../common/Int64Util.ml build/
	cp ../common/DriverUtil.ml build/
	cp ../common/EventHandlers.ml build/
	cp ../common/ITreeExecutor.ml build/
	cp ../common/CProgUtil.ml build/

	cd build/; ocamlopt -a -o acst.cmxa TestInterface.ml console_test.o ctrl1_test.o ctrl2_test.o dev1_test.o dev2_test.o dev3_test.o test_config.o test_interface_impl.o; ocamlopt -o run_cprog.exe acst.cmxa AppSystem.mli AppSystem.ml Int64Util.ml DriverUtil.ml EventHandlers.ml ITreeExecutor.ml CProgUtil.ml Driver.ml

clean:
	rm -rf build
