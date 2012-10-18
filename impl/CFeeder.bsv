import Types::*;

import "BDPI"
function Action initialize(Bool isData, Bit#(32) tId);

import "BDPI"
function ActionValue#(Tuple2#(St, Addr)) getDataFeed(Bit#(32) tId);

import "BDPI"
function ActionValue#(Addr) getInstFeed(Bit#(32) tId);
