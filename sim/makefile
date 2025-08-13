TEST ?= spi_test

dv: clean run_dv

clean:
	\rm -frd novas* mkdir csrc
	\rm -frd ${MODULE}_comp.log ${MODULE}_sim.log ${MODULE}_sim.rpt ${MODULE}_simv ${MODULE}_sim.vcd ${MODULE}_sim.fsdb ${MODULE}_simv.daidir ${MODULE}_ana.log
	\rm -frd ${MODULE}_sim.vcd.vpd
	\rm -frd ucli.key worklib debug.report
	\rm -frd DVEfiles dve_report.* opendatabase.log
	\rm -frd verdiLog inter.fsdb
	\rm -frd seed* sysBusyP* vc_hdrs.h
	\rm -frd bus_cov ${MODULE}_simv.vdb cm.log .fsm.sch.verilog.xml
	\rm -frd qrun sysProgressP.conf sysProgressPLog vdCov.conf vdCovLog
	\rm -frd evaluate_result.fsdb*

#usage: make dv test={ur target tst}
run_dv:
	${ROOT}/sim/run_sim.csh dv ${MODULE} ${test}

fsdb:
	verdi -ssf spi_sim.fsdb &

test_list:
	ls -l ${ROOT}/design/test/
