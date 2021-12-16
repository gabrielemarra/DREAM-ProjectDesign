// Signatures
abstract sig User {
	username : one Username,
	email : one Email
}

sig Username {}{one u:User | u.username=this}

sig Email {}{one u:User | u.email=this}

sig Farmer extends User {
	farm : one Farm, 
	farmerReports : set FarmerReport,
	requests : set Request,
	policyMakerFlag: one Boolean,
	suggestions: set Suggestion
}

sig Farm{
	fields : some Field,
	farmer : one Farmer,
	subarea : one Area
}

// Each Farm belongs to only one farmer and each farmer has only one farm
fact {
	all ff:Farm, f:Farmer|f.farm=ff iff ff.farmer=f
}

//Production data? Production problems?
abstract sig Report{
	timestamp : one Timestamp,
	fieldStatus : one FieldStatus,
	waterUsage : lone WaterUsage,
	harvestAmount : lone HarvestAmount
}

sig FarmerReport extends Report{}

//Each FarmerReport belongs to only one Farmer
fact {
	all f1,f2:Farmer, fr:FarmerReport | ((fr in f1.farmerReports) and (fr in f2.farmerReports)) implies f1=f2
	all fr:FarmerReport | one f:Farmer | fr in f.farmerReports
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
	all fi:Field, f:Farm | (fi in f.fields) iff (fi.farm=f)
}


sig SqMetersArea{}


//TODO
sig Suggestion {}

//All suggestion belongs to different farmers
fact {
	all f1, f2: Farmer, s:Suggestion | ((s in f1.suggestions) and (s in f2.suggestions)) implies f1=f2
}


sig Agronomist extends User {
	subarea : one Area,
	plans : set Plan,
	requests : set Request
}

sig Location {}{one f:Field | f.location=this}


sig Area {
	farms : some Farm,
	agronomists : some Agronomist
}

//A farm belongs to only one Area
fact {
	all a1,a2:Area, f:Farm | ((f in a1.farms) and (f in a2.farms)) implies a1=a2
	all a:Area, f:Farm | (f in a.farms) iff (f.subarea=a)
}

//An Agronomist belongs to only one Area
fact {
	all a1,a2:Area, ag:Agronomist | ((ag in a1.agronomists) and (ag in a2.agronomists)) implies a1=a2
	all a:Area, ag:Agronomist | (ag in a.agronomists) iff (ag.subarea=a)
}

sig Plan {
	visits : some Visit,
	date : one Date,
	confirmed : one Boolean
}

// Each Plan belongs to only one Agronomist
fact {
	all a1,a2:Agronomist, p:Plan | ((p in a1.plans) and (p in a2.plans)) implies a1=a2
	all p:Plan | one a:Agronomist | p in a.plans
}

abstract sig Boolean {}

one sig True, False extends Boolean {}

sig Visit {
	farmers : one Farmer,
	time : one Time,
	duration : one VisitDuration,
	agronomistReport : one AgronimistReport
}

// Each Visit belongs to only one plan
fact{
	all p1,p2:Plan, v:Visit | ((v in p1.visits) and (v in p2.visits)) implies p1=p2
	all v:Visit | one p:Plan | v in p.visits
}

sig VisitDuration{}

sig AgronimistReport extends Report{
	score : one Score
}{one v:Visit|v.agronomistReport = this}

sig Score {}

sig Request{
	messages : some Message,
	farmer : one Farmer,
	agronomist : one Agronomist
}

//One Request belongs to only one Farmer and one Agronomist. Check also if the relation is bidirectional
fact{
	all a1,a2:Agronomist, r:Request| ((r in a1.requests) and (r in a2.requests)) implies a1=a2
	all f1,f2:Farmer, r:Request| ((r in f1.requests) and (r in f2.requests)) implies f1=f2
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

//One Message belongs to only one Request and receiver and sender must be the two Users owning the Request
fact {
	all m:Message | (m.sender=m.request.farmer and m.receiver=m.request.agronomist) or (m.sender=m.request.agronomist and m.receiver=m.request.farmer)
	all r1,r2:Request, m:Message | ((m in r1.messages) and (m in r2.messages)) implies r1=r2
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

//If a fertilizer is suggested for a specific crop, then that crop should be also listed in the suggested crop field 
fact {
	all f:Fertilizer, c:Crop| (f in c.suggestedFertilizers) iff (c in f.suggestedCrops)
}

sig FertilizerName{}{one f:Fertilizer | f.name=this}

sig PolicyMaker extends User {}

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

//Thread belongs to the FORUM
fact {
	all t:Thread, f:Forum | t in f.threads
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
	all t1, t2: Thread, p:Post | ((p in t1.posts) and (p in t2.posts)) implies t1=t2
}

sig PostContent{}

// Each PostContent has one post
fact {
	all pc:PostContent | one p:Post | pc = p.postContent 
}

abstract sig Ranking {
	farmers: some Farmer,
	rankingType: one RankingType
}

sig RankingType{}

sig PolicyRanking extends Ranking{}

//All farmers listed in the Ranking and Rankings
fact {
	all pr:PolicyRanking, f:Farmer | f in pr.farmers
	}

//Two different PolicyRankings with same farmers have different Type
fact {
	all pr1, pr2:PolicyRanking | ((pr1.farmers=pr2.farmers) and (pr1.rankingType=pr2.rankingType)) implies pr1=pr2
}

sig AgronomistRanking extends Ranking{
	allowedAgronomists: set Agronomist,
	area: one Area
}

//Agronomists can see the rankings of only their Area
//Contains only the Farmer in that Area
fact {
	all ar:AgronomistRanking, f:Farmer | (f in ar.farmers) iff (f.farm.subarea=ar.area)
	all ar:AgronomistRanking, a:Agronomist | (a in ar.allowedAgronomists) iff (a.subarea=ar.area)
}

//Two different PolicyRankings with same Area have different Type (check only Area, not farmers and allowedAgronomists)
fact {
	all ar1, ar2:AgronomistRanking | ((ar1.area=ar2.area) and (ar1.rankingType=ar2.rankingType)) implies ar1=ar2
}

pred show{}
run show for 8 but exactly 4 Farmer
