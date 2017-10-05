/*
Copyright 2017 Yoichi Hirai

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/
module votes

abstract sig Node {}
sig SaneNode extends Node {}
sig SlashedNode extends Node {}

sig View {
  v_prev: lone View
}

sig Hash { // actually (H, v)
  h_prev: lone Hash,
  h_view: one View
}

fact {
  no x : Hash | x in x.(^h_prev)
}

fact {
  no x : View | x in x.(^v_prev)
}

// TODO: rename View into Epoch

sig Vote {
  epoch : View,
  checkpoint : Hash,
  source : View,
  sender : one Node // TODO: 'one' here might not be necessary
}

// sig Commit {
//  c_hash : Hash,
//  c_sender: one Node
//}

// sig Prepare {
//  p_hash : Hash,
//  p_view_src : View,
//  p_sender: one Node
//}

fact {
   all vote : Vote | vote.source in (vote.checkpoint.h_view.(^v_prev))
}

pred some_votes {
   some vote : Vote |
     vote.sender in SaneNode
}

fact {
  all h : Hash |
    h.h_prev.h_view = h.h_view.v_prev
}

fact {
  all v0, v1 : View | v0 in v1.(*v_prev) or v1 in v0.(*v_prev)
}

/*
fact {
   { n : Node | n.slashed1 } = { n : Node | not n in SaneNode }
}
*/

/*
pred incompatible_commits {

   some Node &&
   some h0, h1 : Hash | (not h0 in h1.(*h_prev)) &&
    (not h1 in h0.(*h_prev)) &&
    (#{n0 : Node | some c0 : Commit | c0.c_sender = n0 && c0.c_hash = h0}).mul[3] >= (#Node).mul[2] &&
    (#{n1 : Node | some c1 : Commit | c1.c_sender = n1 && c1.c_hash = h1}).mul[3] >= (#Node).mul[2] &&
    (#SlashedNode).mul[3] < (#Node)
}
*/

// how to do the degree of ancestors

// run ownPrev for 10

run some_votes for 4