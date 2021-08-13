.PHONY: all clean

all:
	mkdir -p build
	cp AppSystem.mli build/
	cp AppSystem.ml build/
	cp Driver.ml build/
	cp ../common/Int64Util.ml build/
	cp ../common/DriverUtil.ml build/
	cp ../job_assn_eh/EventHandlers.ml build/
	cp ../common/ITreeExecutor.ml build/

	cd build/; ocamlopt -I build -o run_spec.exe AppSystem.mli AppSystem.ml Int64Util.ml DriverUtil.ml EventHandlers.ml ITreeExecutor.ml Driver.ml

clean:
	rm -rf build
