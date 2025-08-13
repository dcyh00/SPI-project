interface spi_if;
  logic clk;
  logic rst_n;
  logic start;
  logic [7:0] tx_data;
  logic [7:0] rx_data;
  logic busy;
  logic done;
  // SPI interface
  logic sclk;
  logic mosi;
  logic miso;
  logic cs_n;
  logic [7:0] slave_rx_data;
  logic [7:0] slave_send_data;

  // optional modport
  modport drv_mp(
    input   clk,
    output  rst_n,
    output  start,
    output  tx_data,
    input   rx_data,
    input   busy,
    input   done,
    input   sclk,
    input   mosi,
    output  miso,
    input   cs_n,
    input   slave_rx_data, 
    output  slave_send_data 
  );

  modport mon_mp(
    input clk,
    input rst_n,
    input start,
    input tx_data,
    input rx_data,
    input busy,
    input done,
    input sclk,
    input mosi,
    input miso,
    input cs_n,
    input slave_rx_data,
    input  slave_send_data 
  );

  clocking drv_cb @(posedge clk);
    default input #1step output #1;
    output  rst_n;
    output  start;
    output  tx_data;
    input   rx_data;
    input   busy;
    input   done;
    input   sclk;
    input   mosi;
    output  miso;
    input   cs_n;
    input   slave_rx_data;
    output   slave_send_data;
  endclocking

  clocking mon_cb @(posedge clk);
    default input #1step output #1;
    input rst_n;
    input start;
    input tx_data;
    input rx_data;
    input busy;
    input done;
    input sclk;
    input mosi;
    input miso;
    input cs_n;
    input slave_rx_data;
    input slave_send_data;
  endclocking

  task automatic init_tb();
    clk     = 0;
    rst_n   = 0;
    start   = 0;
    tx_data = 0;
    miso    = 0;
  endtask
endinterface
