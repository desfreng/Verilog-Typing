module top ();
  logic signed  [31:0] a;
  logic [10:0] c;
  bit signed  [64:0] d;

  initial begin
    d = signed'(c) + a;
  end
endmodule
