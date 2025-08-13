class spi_seq extends uvm_sequence #(spi_tran);
  `uvm_object_utils(spi_seq)

  int min_delay;
  int max_delay;
  int delay;
  int seq_count;
  int seq_index;
  string seq_type;

  function new(string name = "spi_seq");
    super.new(name);
  endfunction


  task body();
    spi_tran tr;
    `uvm_info(get_type_name(), "Normal Priority Sequence", UVM_MEDIUM)
    repeat (seq_count) begin
      tr = spi_tran::type_id::create("tr");
      start_item(tr);
      tr.randomize();
      finish_item(tr);
    end
  endtask
endclass


