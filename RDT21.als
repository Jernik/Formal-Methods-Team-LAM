module RDT21
open util/ordering[State]

sig Sender{
	buffer: set Data,
	packetSent:DataPacket
}

sig Receiver{
	buffer: set Data
}

sig Data{}

abstract sig SequenceBit{}
one sig SeqZero extends SequenceBit{}
one sig SeqOne extends SequenceBit{}

abstract sig Packet{
	sequenceBit: SequenceBit
}

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
	this.packet.sequenceBit = this.sender.packetSent.sequenceBit
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
			HandleAckPacket[s,s']
		else  //in send state, nackPacket
			HandleNackPacket[s,s']
	else //in receive state
		s.packet not in CorruptedDataPacket => //in receive state, data not corrupted
				HandleGoodDataPacket[s,s']
		else //in receive state, data corrupted
				HandleCorruptDataPacket[s,s']
}

pred HandleAckPacket[s, s': State] {
	s.packet.sequenceBit = s.sender.packetSent.sequenceBit =>
		HandleCorrectAckPacket[s, s']
	else
		HandleNackPacket[s, s']
}

pred HandleCorrectAckPacket[s, s': State] {
		(one d:Data|
		d in s.sender.buffer and d not in s'.sender.buffer
			and s'.packet.data = d and s'.sender.packetSent = s'.packet
		and s'.srState=ReceiveState and s'.packet in DataPacket 
		and s'.sender.buffer = s.sender.buffer - d and s'.receiver.buffer = s.receiver.buffer)
		and not (s'.packet.sequenceBit = s.sender.packetSent.sequenceBit)
}

pred HandleNackPacket[s,s':State]{
	s'.packet.data=s.sender.packetSent.data and s'.packet not = s.sender.packetSent and s'.sender.packetSent not = s.sender.packetSent
		and s'.srState=ReceiveState
		and s'.sender.buffer = s.sender.buffer and s'.receiver.buffer = s.receiver.buffer
		and s'.packet.sequenceBit = s.sender.packetSent.sequenceBit
}

pred HandleGoodDataPacket[s,s':State]{
	s'.receiver.buffer = s.receiver.buffer+s.packet.data and s'.packet in AckPacket and s'.sender.buffer = s.sender.buffer and s'.srState in SendState 
		and s'.sender.packetSent = s.sender.packetSent and s'.packet.sequenceBit = s.sender.packetSent.sequenceBit
}

pred HandleCorruptDataPacket[s,s':State]{
	s'.packet in NackPacket and s'.sender.buffer = s.sender.buffer and s'.receiver.buffer = s.receiver.buffer and s'.srState in SendState
		and s'.sender.packetSent = s.sender.packetSent and s'.packet.sequenceBit = s.sender.packetSent.sequenceBit
}

pred TestHandleAckPacket[] {
	first.init
	Step[first,first.next] and Step[first.next,first.next.next] and HandleAckPacket[first.next.next,first.next.next.next]
}

pred TestHandleNackPacket[] {
	first.init
	Step[first,first.next] and first.next.packet in CorruptedDataPacket
	and Step[first.next,first.next.next]
	and HandleNackPacket[first.next.next,first.next.next.next]
	and Step[first.next.next,first.next.next.next] and first.next.next.next.packet not in CorruptedDataPacket

}

run TestHandleNackPacket for 5 but 2 Data

pred State.end{
	this.receiver.buffer = Data
	no this.sender.buffer
}

pred Trace {
	first.init
	all s: State - last |
		let s' = s.next |
			(Step[s, s'])
//	last.end // makes sure that we actually find a result
}

assert allDataCanBeTransferred{
	Trace => last.end
}

assert allDataCanBeTransferredWithErrorLimit{
	(atMostOneCorrupt and Trace) => last.end
}

pred oneCorrupt{
	#(CorruptedDataPacket)>=1
}
pred atLeastOneNotCorrupt{
	#(DataPacket-CorruptedDataPacket)>=1
}
pred atMostOneCorrupt{
	all d: DataPacket - CorruptedDataPacket | lone c : CorruptedDataPacket | d.data = c.data
}
pred atleastTwoData{
	#(Data) = 3
}



run Trace for 8 but exactly 3 Data
check allDataCanBeTransferred for 4 but 2 Data
check allDataCanBeTransferredWithErrorLimit for 8 but 2 Data
