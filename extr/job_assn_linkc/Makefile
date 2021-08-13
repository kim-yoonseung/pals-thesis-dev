.PHONY: all clean

all:
	mkdir -p build
	cp ../../cdev/build/test_interface_impl.o build/
	cp ../../cdev/apps/job-assn/build/test_config.o build/
	cp ../../cdev/apps/job-assn/build/*_test.o build/
	cp ../generic/Generic.mli build/AppSystem.mli
	cp ../generic/Generic.ml build/AppSystem.ml
	cp Driver.ml build/
	cp ../common/TestInterface.ml build/
	cp ../common/Int64Util.ml build/
	cp ../common/DriverUtil.ml build/
	cp ../job_assn_eh/EventHandlers.ml build/
	cp ../job_assn_eh/EventImplInterface.ml build/
	cp ../job_assn_eh/event_impl.c build/
	cp ../common/ITreeExecutor.ml build/
	cp ../common/CProgUtil.ml build/

	cd build/; ocamlopt -a -o acst.cmxa TestInterface.ml master_test.o worker1_test.o worker2_test.o worker3_test.o worker4_test.o worker5_test.o worker6_test.o worker7_test.o worker8_test.o test_config.o test_interface_impl.o; ocamlopt -c event_impl.c; ocamlopt -a -o eventimpl.cmxa EventImplInterface.ml event_impl.o; ocamlopt -o run_cprog.exe acst.cmxa eventimpl.cmxa AppSystem.mli AppSystem.ml Int64Util.ml DriverUtil.ml EventHandlers.ml ITreeExecutor.ml CProgUtil.ml Driver.ml

clean:
	rm -rf build
