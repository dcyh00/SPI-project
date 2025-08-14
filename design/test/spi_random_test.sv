class spi_random_test extends spi_test;
  `uvm_component_utils(spi_random_test)

	random_seq seq;
	int seq_count = 10;
  int seq_min_delay = 0, seq_max_delay = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    seq = random_seq::type_id::create("seq");

    seq.seq_count = this.seq_count;

    phase.raise_objection(this);
    seq.start(env.agt.sqr);
    phase.drop_objection(this);
  endtask

endclass

