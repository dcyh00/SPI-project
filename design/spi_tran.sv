class spi_tran extends uvm_sequence_item;
  rand bit rst_n;
  rand bit start;
  rand bit miso;
  rand bit [7:0] tx_data;
  rand bit [3:0] cmd;

  logic [7:0] rx_data;
  logic busy;
  logic done;
  logic sclk;
  logic mosi;
  logic cs_n;
  logic [7:0] slave_rx_data;
  rand logic [7:0] slave_send_data;

  int seq_count;
  int seq_index;
  int tran_count;
  int tran_index;
  string seq_type;
  string tran_type;

  `uvm_object_utils(spi_tran)

  function new(string name = "spi_tran");
    super.new(name);
  endfunction
endclass
