module RDT20
open util/ordering[State]

sig Sender{
	buffer: set Data,
	packetSent:DataPacket
}

sig Receiver{
	buffer: set Data
}

sig Data{}

abstract sig Packet{}

sig DataPacket extends Packet{
	data: Data
}
sig CorruptedDataPacket extends DataPacket{}

abstract sig ResponsePacket extends Packet{}
sig AckPacket extends ResponsePacket{}
sig NackPacket extends ResponsePacket{}



abstract sig SendReceiveState{}
one sig SendState extends SendReceiveState{}
one sig ReceiveState extends SendReceiveState{}



sig State{
	sender: Sender,
	receiver: Receiver,
	packet:Packet,
	srState: SendReceiveState
}

pred State.init{
	this.sender.buffer = Data
	no this.receiver.buffer
	this.packet in AckPacket
	this.srState in SendState
}


//create packet from data in sender.buffer
//receive packet in receiver
//check corruption in packet
//send ack/nak to sender
//sender doesnt send data if no ack received
pred Step[s, s': State]{
	s.srState in SendState=> //in send state
		s.packet in AckPacket => //in send state, ackPacket
			(one d:Data|
				d in s.sender.buffer and d not in s'.sender.buffer and s'.packet.data = d and s'.sender.packetSent = s'.packet
				and s'.srState=ReceiveState and s'.packet in DataPacket 
				and s'.sender.buffer = s.sender.buffer - d and s'.receiver.buffer = s.receiver.buffer)
		else  //in send state, nackPacket
			s'.packet.data=s.sender.packetSent.data and s'.packet not = s.sender.packetSent
			and s'.srState=ReceiveState
			and s'.sender.buffer = s.sender.buffer and s'.receiver.buffer = s.receiver.buffer
		else //in receive state
			s.packet not in CorruptedDataPacket => //in receive state, data not corrupted
				s'.receiver.buffer = s.receiver.buffer+s.packet.data and s'.packet in AckPacket and s'.sender.buffer = s.sender.buffer and s'.srState in SendState 
				and s'.sender.packetSent = s.sender.packetSent
			else //in receive state, data corrupted
				s'.packet in NackPacket and s'.sender.buffer = s.sender.buffer and s'.receiver.buffer = s.receiver.buffer and s'.srState in SendState
					and s'.sender.packetSent = s.sender.packetSent
}

pred State.end{
	first.sender.buffer = this.receiver.buffer
	no this.sender.buffer
}

pred Trace {
	first.init
	all s: State - last |
		let s' = s.next |
			(Step[s, s'])  or Progress[s,s'])
	last.end
}


assert allDataCanBeTransferred{
	Trace => last.end
}
fact oneCorrupt{
	#(CorruptedDataPacket)>=1
}
fact atLeastOneNotCorrupt{
	#(DataPacket-CorruptedDataPacket)>=1
}
/*fact atLeastOneResponse{
	#(ResponsePacket)>1
}
//used for debug
*/fact atleastTwoData{
	#(Data) = 3
}



run Trace for 6
check allDataCanBeTransferred
