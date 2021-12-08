// Signatures
abstract sig User {
	username : one Username,
	email : one Email
}

sig Username {}

sig Email {}

sig Farmer extends User {
	farm : lone Farm, 
	reports : set Report
}

sig Farm{
	fields : some Field,
	farmer : one Farmer,
	subarea : one Area
}

//Production data? Production problems?
sig Report{
	timestamp : one Timestamp,
	fieldStatus : one FieldStatus,
	waterUsage : lone Int,
	harvestAmount : lone Int
}

sig FieldStatus {
	crop : lone Crop,
	fertilizer : lone Fertilizer,

}

sig Field{
	farm : one Farm,
	location : one Location,
	sqMeters : one Int,
	currentStatus : one FieldStatus
}

sig Agronomist extends User {
	subarea : lone Area,
	plans : set Plan,
	requests : set Request
}

sig Location {
	latitude : one Latitude,
	longitude : one Longitude
}

sig Latitude{}
sig Longitude{}

sig Area {
	farms : some Farm,
	agronomists : some Agronomist
}

sig Plan {
	visits : some Visit,
	date : one Date
}

sig Visit {
	farmers : one Farmer,
	time : one Time,
	duration : one Int,
	report : one AgronimistReport
}

sig AgronimistReport extends Report{
	score : one Int
}

sig Request{
	messages : some Message,
	farmer : one Farmer,
	agronomist : one Agronomist
}

sig Message {
	request : one Request,
	content : one String,
	sender : one User, 
	receiver : one User,
	timestamp : one Timestamp
}

sig Crop {
	name : one String,
	suggestedFertilizers : set Fertilizer
}
sig Date {}
sig Time {}
sig Timestamp{
	date : one Date,
	time : one Time
}

sig Fertilizer {
	name : one String,
	suggestedCrops : set Crop
}

sig WaterUsage {}

sig PolicyMaker extends User {
	
}

sig Forum {
	threads: set Thread
}

sig Thread {
	title : one String,
	posts : some Post,
	creator : one Farmer,
	timestamp : one Timestamp
}

sig Post {
	thread : one Thread,
	content : one String,
	creator : one User, //assert that only farmers and agronomist create post
	timestamp : one Timestamp
}
	
