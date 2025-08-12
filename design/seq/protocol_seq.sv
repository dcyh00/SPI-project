class protocol_seq extends spi_seq;
	`uvm_object_utils(protocol_seq)

	function new(string name = "spi_seq");
    		super.new(name);
  	endfunction

	task body();
		
		spi_tran tr;
    		`uvm_info(get_type_name(), "Protocol SEQ", UVM_MEDIUM)
		repeat (10) begin
			tr= spi_tran::type_id::create("tr");
			start_item(tr);
			tr.randomize() with {start==1;};
			finish_item(tr);
		end
	endtask

endclass
