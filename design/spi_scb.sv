class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp;

  int passed_count = 0;
  int failed_count = 0;
  int tran_count;
  int tran_index;
  string tran_type;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    scb_imp = new("scb_imp", this);
  endfunction

  function void write(spi_tran tr_dut);

	if(tr_dut.done) begin
		tx_compare(tr_dut);
		rx_compare(tr_dut);
	end

  endfunction

  function void report_phase(uvm_phase phase);
    //`uvm_info("SCOREBOARD", $sformatf("Test Complete. Passed: %0d Failed: %0d", passed_count, failed_count), UVM_NONE)
  endfunction
	
	function tx_compare(spi_tran tr_dut);
		
		//this one is to compare the tx_data with the sampled data in
		//slave
		if(tr_dut.tx_data !== tr_dut.slave_rx_data) begin
			`uvm_error(get_type_name(), $sformatf("[ERROR] Expected slave sampled_data = %h, Actual = %h", tr_dut.tx_data, tr_dut.slave_rx_data))
		end
		else `uvm_info(get_type_name(), $sformatf("[PASS] Expected slave sampled_data = %h, Actual = %h", tr_dut.tx_data, tr_dut.slave_rx_data), UVM_LOW)

	endfunction

	function rx_compare(spi_tran tr_dut);
		
		//this one is to compare the tx_data with the sampled data in
		//slave
		if(tr_dut.rx_data !== 8'hb9) begin
			`uvm_error(get_type_name(), $sformatf("[ERROR] Expected slave sampled_data = %h, Actual = %h", 8'hb9, tr_dut.rx_data))
		end
		else `uvm_info(get_type_name(), $sformatf("[PASS] Expected slave sampled_data = %h, Actual = %h", 8'hb9, tr_dut.rx_data), UVM_LOW)

	endfunction
endclass
