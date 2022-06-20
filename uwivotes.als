module uwiVotes

//SYSTEM ELEMENTS
sig Election, Date, Position, Faculty, Hall, Email, Ballot {}
sig Candidate, Voter {}

abstract sig ifStarted {}
one sig HasNotStarted, HasStarted, HasEnded extends ifStarted {}

abstract sig ifCommute {}
one sig DoesCommute, DoesntCommute extends ifCommute {}

abstract sig ifGraduate {}
one sig isGraduate, IsntGraduate extends ifGraduate {}

abstract sig ifVoted {}
one sig HasntVoted, HasVoted extends ifVoted {}

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
    voterBallot: voters -> ballots
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
    
    /* General Constraints
        The following block contains all general constraints English. They 
        are formally specified in the same order as listed below:
        - election must have a start and end date
        - election must have a start status
        - emails must be associated to a candidate or a voter
        - if email is the same between a candidate and a voter, then the graduate and commute status must be the same (considered the same person)
    */
    
    all election: uv.election | one election.(uv.electionStart) and one election.(uv.electionEnd)
    all election: uv.election | one election.(uv.electionStatus)
    all email: uv.emails | one uv.voterEmails.email or one uv.candidateEmails.email
    let ve = uv.voterEmails, ce = uv.candidateEmails{
        all candidate: uv.candidates, voter: uv.voters | some (candidate.ce & voter.ve) implies candidate.(uv.candidateGStatus) = voter.(uv.voterGStatus)
        all candidate: uv.candidates, voter: uv.voters | some (candidate.ce & voter.ve) implies candidate.(uv.candidateCStatus) = voter.(uv.voterCStatus)
    }
}

//FACTS - correct this when complete 
fact {all uv:uwiVotes | inv[uv]}

//OPERATIONS (??)

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
} run init for 4 but 1 uwiVotes expect 1

pred sanityCheck{
    some uv: uwiVotes{
        some uv.election
        #uv.halls = 2
        #uv.faculties = 2
        #uv.positions = 2	
	    #uv.voters = 2
        #candidates = 2
    }
} run sanityCheck for 4 but 1 uwiVotes expect 1

