class protocol_seq extends spi_seq;
	`uvm_object_utils(protocol_seq)
	
	rand bit [7:0] tx_data;
	rand bit miso;
	rand bit start_bit;
	rand bit cmd;
	rand logic [7:0] slave_send_data;
	function new(string name = "spi_seq");
    		super.new(name);
  	endfunction

	task body();
		
		spi_tran tr;
			tr= spi_tran::type_id::create("tr");
			start_item(tr);
			tr.randomize()  with{
				cmd		==	local::cmd;
				tx_data 	== 	local::tx_data;
				//start_bit	==	local::start_bit;
				miso		==	local::miso;
				slave_send_data	==	local::slave_send_data;};
			finish_item(tr);
	endtask

endclass
