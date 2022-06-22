module uwiVotes
open util/ordering[uwiVotes] as uwiV

//SYSTEM ELEMENTS
sig Election, Date, Position, Faculty, Hall, Email, Ballot, Vote {}
sig Candidate, Voter {}

abstract sig ifStarted {}
one sig HasNotStarted, HasStarted, HasEnded extends ifStarted {}

abstract sig ifCommute {}
one sig DoesCommute, DoesntCommute extends ifCommute {}

abstract sig ifGraduate {}
one sig isGraduate, IsntGraduate extends ifGraduate {}

abstract sig ifVoted {}
one sig Voted,  HasntVoted extends ifVoted {}

abstract sig ifSubmitted {}
one sig HasntSubmitted, Submitted extends ifSubmitted {}

//UWIVOTES - Closed System Rep
sig uwiVotes {
    //Relations
    election: one Election,
    sDate: one Date,
    eDate: one Date,
    candidates: set Candidate,
    positions: set Position,
    faculties: set Faculty,
    halls: set Hall,
    voters: set Voter,
    emails: set Email,
    voteStats: set ifVoted,
    gradStats: set ifGraduate,
    commuteStats: set ifCommute,
    electStats: one ifStarted,
    ballots: set Ballot,
    votes: set Vote,
    submitStats: set ifSubmitted,

    //Constraints
    electCandidates: election -> candidates,
    electionStart: election -> sDate,
    electionEnd: election -> eDate,
    electionStatus: election -> electStats,
    electVoters: election -> voters,
    candidateEmails: candidates -> emails,
    candidatePos: candidates -> positions,
    candidateFaculty : candidates -> faculties,
    candidateHall : candidates -> halls,
    voterEmails: voters -> emails,
    voterFaculty : voters -> faculties,
    voterHall: voters -> halls,
    voterVStatus: voters -> voteStats,
    voterGStatus: voters -> gradStats,
    voterCStatus: voters -> commuteStats,
    candidateGStatus: candidates -> gradStats,
    candidateCStatus: candidates -> commuteStats,
    voterBallot: voters -> ballots,
    ballotVotes: ballots -> votes,
    ballotSState: ballots -> submitStats
}

//PREDICATES 
pred inv [uv: uwiVotes]{
    /* Candidate Constraints
        The following block contains the constraints specific to candidates in English. They 
        are formally specified in the same order as listed below:
        - candidates must be associated with an election
        - candidates can only belong to one faculty
        - candidates can only belong to one hall
        - candidates must have an email
        - emails among candidates must be unique
        - candidates may only go up for one position
        - candidates must have graduate status
        - candidates must have commute status
    */
    
    all candidate: uv.candidates | one uv.electCandidates.candidate
    all candidate: uv.candidates | one candidate.(uv.candidateHall)
    all candidate: uv.candidates | one candidate.(uv.candidateFaculty)
    all candidate: uv.candidates | one candidate.(uv.candidateEmails)
	let ce = uv.candidateEmails {
		all disj c1, c2: uv.candidates|  no (c1.ce & c2.ce)
	}
    all candidate: uv.candidates | one candidate.(uv.candidatePos)
    all candidate: uv.candidates | one candidate.(uv.candidateGStatus)
    all candidate: uv.candidates | one candidate.(uv.candidateCStatus)

    /* Voters Constraints
        The following block contains the constraints specific to voters in English. They 
        are formally specified in the same order as listed below:
        - voters must be associated with an election
        - voters can only belong to one faculty
        - voters can only belong to one hall
        - voters must have an email
        - emails among voters must be unique
        - no two voters must have the same ballot
        - voters must have a vote status
        - voters must have graduate status
        - voters must have commute status
        - voters must have a ballot
        - if a voter commutes and is a graduate, they should have at least 2 votes on their ballot
        - if a voter has voted then their ballot must be in its submitted state 
            - Likewise, if a ballot is in its submitted state then the assciated voter must have voted
        - if a voter has not voted then their ballot should be in its not submitted state (further enforcing the above)
    */

    all voter: uv.voters | one uv.electVoters.voter
    all voter: uv.voters | one voter.(uv.voterHall)
    all voter: uv.voters | one voter.(uv.voterFaculty)
    all voter: uv.voters | one voter.(uv.voterEmails)
    let ve = uv.voterEmails {
        all disj v1, v2: uv.voters| no (v1.ve & v2.ve)
    }
    let ba = uv.voterBallot {
        all disj v1,v2:uv.voters | no (v1.ba & v2.ba)
    } 
    all voter: uv.voters | one voter.(uv.voterVStatus)
    all voter: uv.voters | one voter.(uv.voterGStatus)
    all voter: uv.voters | one voter.(uv.voterCStatus)
    all voter: uv.voters | one voter.(uv.voterBallot)
    let vcs = uv.voterCStatus, vgs = uv.voterGStatus, vb = uv.voterBallot {
        all voter: uv.voters | (voter.vcs = DoesCommute) and (voter.vgs = isGraduate) implies #((voter.vb).(uv.ballotVotes)) >= 2
    }
    let vvs = uv.voterVStatus, bss = uv.ballotSState{
        all voter: uv.voters | voter.vvs = Voted iff (voter.(uv.voterBallot)).bss = Submitted
        all voter: uv.voters | voter.vvs = HasntVoted iff (voter.(uv.voterBallot)).bss = HasntSubmitted
    }
    
    /* General Constraints
        The following block contains all general constraints English. They 
        are formally specified in the same order as listed below:
        - election must have a start and end date
        - election must have a start status
        - emails must be associated to a candidate or a voter
        - if email is the same between a candidate and a voter, then the graduate and commute status must be the same (considered the same person)
        - if email is the same between a candidate and a voter, then the faculty and hall hould be the same (considered same person)
        - no voter should submit an empty ballot (no categories)
        - all votes must be associated with atleast one ballot
        - number of votes any ballot has should never exceed the number of positions
        - all ballots must belong to a voter
        - all ballots must have a submit state
        - a ballot can only be in it's submitted state if the election HasStarted or HasEnded (tba)
    */
    
    all election: uv.election | one election.(uv.electionStart) and one election.(uv.electionEnd)
    all election: uv.election | one election.(uv.electionStatus)
    all email: uv.emails | one uv.voterEmails.email or one uv.candidateEmails.email
    let ve = uv.voterEmails, ce = uv.candidateEmails{
        all candidate: uv.candidates, voter: uv.voters | some (candidate.ce & voter.ve) implies candidate.(uv.candidateGStatus) = voter.(uv.voterGStatus)
        all candidate: uv.candidates, voter: uv.voters | some (candidate.ce & voter.ve) implies candidate.(uv.candidateCStatus) = voter.(uv.voterCStatus)
        all candidate: uv.candidates, voter: uv.voters | some (candidate.ce & voter.ve) implies candidate.(uv.candidateHall) = voter.(uv.voterHall)
        all candidate: uv.candidates, voter: uv.voters | some (candidate.ce & voter.ve) implies candidate.(uv.candidateFaculty) = voter.(uv.voterFaculty)
    }
    all ballot: uv.ballots | some ballot.(uv.ballotVotes)
    all votes: uv.votes | some uv.ballotVotes.votes
    all ballot: uv.ballots | #(ballot.(uv.ballotVotes)) <= #(uv.candidatePos)
    all ballot: uv.ballots | one uv.voterBallot.ballot
    all ballot: uv.ballots | one ballot.(uv.ballotSState)
}

private pred noChange[preUV, postUV: uwiVotes]{
    preUV.election = postUV.election
    preUV.sDate = postUV.sDate
    preUV.eDate = postUV.eDate
    preUV.candidates = postUV.candidates
    preUV.positions = postUV.positions
    preUV.faculties = postUV.faculties
    preUV.halls = postUV.halls
    preUV.voters = postUV.voters
    preUV.emails = postUV.emails
    preUV.voteStats = postUV.voteStats
    preUV.gradStats = postUV.gradStats
    preUV.commuteStats = postUV.commuteStats
    preUV.electStats = postUV.electStats
    preUV.ballots = postUV.ballots
    preUV.votes = postUV.votes
    preUV.submitStats = postUV.submitStats
    preUV.electCandidates = postUV.electCandidates
    preUV.electionStart = postUV.electionStart
    preUV.electionEnd = postUV.electionEnd
    preUV.electionStatus = postUV.electionStatus
    preUV.electVoters = postUV.electVoters
    preUV.candidateEmails = postUV.candidateEmails
    preUV.candidatePos = postUV.candidatePos
    preUV.candidateFaculty = postUV.candidateFaculty
    preUV.candidateHall = postUV.candidateHall
    preUV.voterEmails = postUV.voterEmails 
    preUV.voterFaculty = postUV.voterFaculty
    preUV.voterHall = postUV.voterHall
    preUV.voterVStatus = postUV.voterVStatus
    preUV.voterGStatus = postUV.voterGStatus
    preUV.voterCStatus = postUV.voterCStatus
    preUV.candidateGStatus = postUV.candidateGStatus
    preUV.candidateCStatus = postUV.candidateCStatus
    preUV.voterBallot = postUV.voterBallot
    preUV.ballotVotes = postUV.ballotVotes
    preUV.ballotSState = postUV.ballotSState
}

pred skip[preUV, postUV: uwiVotes] {
    noChange[preUV, postUV]
} run skip for 4 but 1 uwiVotes expect 1
run skip for 4 but 2 uwiVotes expect 1

//FACTS
fact traces {
    init[uwiV/first]
    inv[uwiV/first]
    all uv: uwiVotes - uwiV/last |
        let uvNext = uv.next |
            some uv1,uv2: uwiVotes, v: Voter, b: Ballot, e: Election |
        skip[uv, uvNext] or
            submitBallot[uv1,uv2,v,b,e] //currently causing counter examples in initEstablishes
} run {} for 7 but 5 uwiVotes expect 1

//OPERATIONS
pred submitBallot[preUV, postUV: uwiVotes, voter: Voter, ballot: Ballot, elect: Election]{
    /*  Pre Conditions
         The following are the preconditions for the submitBallot operation in English.They 
         are formally specified in the same order as listed below: 
         - ballot must exist
         - ballot must not be submitted
         - voter must not have voted
         - election must have started
    */
    ballot in univ.(preUV.voterBallot)
    ballot.(preUV.ballotSState) = HasntSubmitted
    voter.(preUV.voterVStatus) = HasntVoted
    elect.(preUV.electionStatus) = HasStarted

    /* Post Conditions
        The following are the preconditions for the submitBallot operation in English.They 
         are formally specified in the same order as listed below: 
         - ballot must now be submitted
         - voter must now have voted
         - enforcing ifVoted & ifSubmitted Constraints
         - enforcing ballotSState Constraint
    */

    ballot.(postUV.ballotSState) = Submitted
    voter.(postUV.voterVStatus) = Voted
	let vvs = postUV.voterVStatus, bss = postUV.ballotSState{
        all voter: postUV.voters | voter.vvs = Voted iff (voter.(postUV.voterBallot)).bss = Submitted
	    all voter: postUV.voters | voter.vvs = HasntVoted iff (voter.(postUV.voterBallot)).bss = HasntSubmitted
    }
    all ballot: postUV.ballots | one ballot.(postUV.ballotSState)

    //FRAMECONDITIONS
    preUV != postUV
    preUV.election = postUV.election
    preUV.sDate = postUV.sDate
    preUV.eDate = postUV.eDate
    preUV.candidates = postUV.candidates
    preUV.positions = postUV.positions
    preUV.faculties = postUV.faculties
    preUV.halls = postUV.halls
    preUV.voters = postUV.voters
    preUV.emails = postUV.emails
    preUV.voteStats = postUV.voteStats
    preUV.gradStats = postUV.gradStats
    preUV.commuteStats = postUV.commuteStats
    preUV.electStats = postUV.electStats
    preUV.ballots = postUV.ballots
    preUV.votes = postUV.votes
    preUV.submitStats = postUV.submitStats
    preUV.electCandidates = postUV.electCandidates
    preUV.electionStart = postUV.electionStart
    preUV.electionEnd = postUV.electionEnd
    preUV.electionStatus = postUV.electionStatus
    preUV.electVoters = postUV.electVoters
    preUV.candidateEmails = postUV.candidateEmails
    preUV.candidatePos = postUV.candidatePos
    preUV.candidateFaculty = postUV.candidateFaculty
    preUV.candidateHall = postUV.candidateHall
    preUV.voterEmails = postUV.voterEmails 
    preUV.voterFaculty = postUV.voterFaculty
    preUV.voterHall = postUV.voterHall
    preUV.voterGStatus = postUV.voterGStatus
    preUV.voterCStatus = postUV.voterCStatus
    preUV.candidateGStatus = postUV.candidateGStatus
    preUV.candidateCStatus = postUV.candidateCStatus
    preUV.voterBallot = postUV.voterBallot
    preUV.ballotVotes = postUV.ballotVotes
#preUV.ballotSState = #postUV.ballotSState
    #preUV.voterVStatus = #postUV.voterVStatus
} run submitBallot for 4 but 2 uwiVotes expect 1

//INSTANCES
pred init [uv:uwiVotes]{
    some election
    some sDate
    some eDate
    some candidates
    some positions
    some faculties
    some halls
    some voters
    some emails
    some voteStats
    some gradStats
    some commuteStats
    some electStats
    some ballots
    some votes
    some submitStats
    some electCandidates
    some electionStart
    some electionEnd
    some electionStatus
    some electVoters
    some candidateEmails
    some candidatePos
    some candidateFaculty
    some candidateHall
    some voterEmails
    some voterFaculty
    some voterHall
    some voterVStatus
    some voterGStatus
    some voterCStatus
    some candidateGStatus
    some candidateCStatus
    some voterBallot
    some ballotVotes
    some ballotSState
} run init for 4 but 1 uwiVotes expect 1

pred sanityCheck{
    some uv: uwiVotes{
        some uv.election
        #uv.halls = 2
        #uv.faculties = 2
        #uv.positions = 2
        #uv.voters = 2
        #uv.candidates = 2
        #uv.votes = 4
    }
} run sanityCheck for 4 but 1 uwiVotes expect 1

//ASSERTIONS
assert initEstablishes{
	all uv: uwiVotes| init[uv] implies inv[uv]
}check initEstablishes

assert submitBallotPreserves{
	all preUV, postUV: uwiVotes, voter: Voter, ballot: Ballot, elect: Election|
		inv[preUV] and submitBallot[preUV, postUV, voter, ballot, elect]
			implies inv[postUV]
} check submitBallotPreserves for 7 expect 0 
