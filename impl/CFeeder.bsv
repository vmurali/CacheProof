import Types::*;

import "BDPI"
function Action initialize(Bool isData, Bit#(32) tId);

import "BDPI"
function ActionValue#(St) getDataSt(Bit#(32) tId);

import "BDPI"
function ActionValue#(Addr) getFeed(Bool isData, Bit#(32) tId);
