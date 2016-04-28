module RDT10
open util/ordering[State]

one sig Sender{
	buffer: set Data
}
one sig Receiver{
	buffer:set Data	
}

sig Data{}

sig State{
	sender: Sender,
	receiver: Receiver
}


