module uwiVotes

//SYSTEM ELEMENTS
sig Election, Candidate, Position, Faculty, Hall, Email, Voter {}
sig Date {}

abstract sig ifStarted {}
one sig HasNotStarted, HasStarted, HasEnded extends ifStarted {}

abstract sig ifCommute {}
one sig DoesCommute, DoesntCommute extends ifCommute {}

abstract sig ifGraduate {}
one sig isGraduate, IsntGraduate extends ifGraduate {}

abstract sig ifVoted {}
one sig HasVoted, HasntVoted extends ifVoted {}

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

    //Constraints
    electCandidates: election -> candidates,
    electionStart: election -> sDate,
    electionEnd: election -> eDate,
    votersList: election -> voters -> emails,
    candiateEmails: candidates -> emails,
    candidatePos: candidates -> positions,
    candidateFaculty : candidates -> faculties,
    candidateHall : candidates -> halls,
    voterEmails: voters -> emails,
    voterFaculty : voters -> faculties,
    voterHall: voters -> halls,
    voterStatus: voters -> voteStats

}

//PREDICATES 
pred inv [uv: uwiVotes]{
    //insert invariants

    --voters can only be in one faculty && hall
    --candidates can only be in one faculty && hall
    --emails must be unique to the person (if a candiate is a voter or reverse, email is same)
    --a candidate cannot be up for more than one position
}

//OPERATIONS (??)

//INSTANCES