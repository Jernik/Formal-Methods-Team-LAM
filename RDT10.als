module RDT10
open util/ordering[State]

sig Sender{
	buffer: set Data
}

sig Receiver{
	buffer: set Data	
}

some sig Data{}

sig State{
	sender: Sender,
	receiver: Receiver
}

pred State.init{
	this.sender.buffer = Data
	no this.receiver.buffer
}

pred Step[s, s': State]{
	one d:Data|
		d in s.sender.buffer and d in s'.receiver.buffer and d not in s.receiver.buffer and d not in s'.sender.buffer and
		s'.sender.buffer = s.sender.buffer-d and s'.receiver.buffer - d  = s.receiver.buffer
}

pred State.end{
	first.sender.buffer = this.receiver.buffer
	no last.sender.buffer
}

fact Trace {
	first.init
	all s: State - last |
		let s' = s.next |
			(Step[s, s'] or s.end)
	last.end
}

pred someDataCanBeTransferred{

}

assert allDataCanBeTransferred{
	first.init => last.end
}

//used for debug
/*fact atleastTwoData{
	#(Data) =2
}
*/


run someDataCanBeTransferred for 3
check allDataCanBeTransferred

