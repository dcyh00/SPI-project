class random_seq extends spi_seq;
	`uvm_object_utils(random_seq)

	function new(string name = "spi_seq");
		super.new(name);
	endfunction

	task body();
		spi_tran tr;
		`uvm_info(get_type_name(), "Random SEQ", UVM_MEDIUM)
		repeat (seq_count) begin
			tr= spi_tran::type_id::create("tr");
			start_item(tr);
			tr.randomize();
			finish_item(tr);
		end
	endtask

endclass
