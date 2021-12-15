// Signatures
abstract sig User {
	username : one Username,
	email : one Email
}

sig Username {}{one u:User | u.username=this}

sig Email {}{one u:User | u.email=this}

sig Farmer extends User {
	farm : one Farm, 
	reports : set Report,
	requests : set Request
}

sig Farm{
	fields : some Field,
	farmer : one Farmer,
	subarea : one Area
}

// Each Farm belongs to only one farmer and each farmer has only one farm
fact {
	all ff:Farm | one f:Farmer|f.farm=ff and ff.farmer=f
}

//Production data? Production problems?
sig Report{
	timestamp : one Timestamp,
	fieldStatus : one FieldStatus,
	waterUsage : lone WaterUsage,
	harvestAmount : lone HarvestAmount
}

sig WaterUsage{}

sig HarvestAmount{}

sig FieldStatus {
	crop : lone Crop,
	fertilizer : lone Fertilizer,
}

sig Field{
	farm : one Farm,
	location : one Location,
	sqMeters : one SqMetersArea,
	currentStatus : one FieldStatus
}

// Each Field belongs to only one farm and the relation is bidirectional
fact {
	all fi:Field | one f:Farm| (fi in f.fields) and (fi.farm=f)
	all fi:Field | #{f:Farm | fi in f.fields}=1
}


sig SqMetersArea{}

sig Agronomist extends User {
	subarea : lone Area,
	plans : set Plan,
	requests : set Request
}

sig Location {}{one f:Field | f.location=this}


sig Area {
	farms : some Farm,
	agronomists : some Agronomist
}

sig Plan {
	visits : some Visit,
	date : one Date,
	confirmed : one Boolean
}

sig Boolean {}

one sig True, False extends Boolean {}

sig Visit {
	farmers : one Farmer,
	time : one Time,
	duration : one VisitDuration,
	report : one AgronimistReport
}

sig VisitDuration{}

sig AgronimistReport extends Report{
	score : one Score
}

sig Score {}

sig Request{
	messages : some Message,
	farmer : one Farmer,
	agronomist : one Agronomist
}

//One Request belongs to only one Farmer and one Agronomist. Check also if the relation is bidirectional
fact{
	all r:Request | #{a:Agronomist | r in a.requests}=1
	all r:Request | #{f:Farmer | r in f.requests}=1
	all r:Request | one a:Agronomist | (r in a.requests) and (r.agronomist=a)
	all r:Request | one f:Farmer | (r in f.requests) and (r.farmer=f)
}

sig Message {
	request : one Request,
	messageContent : one MessageContent,
	sender : one User, 
	receiver : one User,
	timestamp : one Timestamp
}{one r:Request | (request = r) and ( this in r.messages)}

//One Message belongs to only one Request and receiver and sender must be the two User owning in the Request
fact {
	all m:Message | (m.sender=m.request.farmer and m.receiver=m.request.agronomist) or (m.sender=m.request.agronomist and m.receiver=m.request.farmer)
	all m:Message | #{r:Request | m in r.messages}=1
}

sig MessageContent{}{one m:Message | m.messageContent=this}

sig Crop {
	name : one CropName,
	suggestedFertilizers : set Fertilizer
}

sig CropName{}{one c:Crop | c.name=this}
sig Date {}
sig Time {}
sig Timestamp{
	date : one Date,
	time : one Time
}

sig Fertilizer {
	name : one FertilizerName,
	suggestedCrops : set Crop
}

sig FertilizerName{}{one f:Fertilizer | f.name=this}



sig PolicyMaker extends User {
	
}

//Only one Forum possible - Singleton
one sig Forum {
	threads: set Thread
}

sig Thread {
	title : one ThreadTitle,
	posts : some Post,
	creator : one Farmer,
	timestamp : one Timestamp
}

sig ThreadTitle {}

// Each ThreadTitle has one thread
fact {
	all tt:ThreadTitle | one t:Thread | tt = t.title
}

sig Post {
	thread : one Thread,
	postContent : one PostContent,
	creator : one Farmer,
	timestamp : one Timestamp
}

// Check bidirectional relation between Post and Thread
fact {
	all p:Post | one t:Thread | (p.thread = t) and (p in t.posts)
}

sig PostContent{}

// Each PostContent has one thread
fact {
	all pc:PostContent | one p:Post | pc = p.postContent 
}
	

pred show{}
run show for 8 but exactly 2 Request, exactly 9 Message, exactly 9 MessageContent, exactly 4 Farmer, exactly 4 Agronomist
