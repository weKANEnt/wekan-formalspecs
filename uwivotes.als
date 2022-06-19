module uwiVotes

//SYSTEM ELEMENTS
sig Election, Candidate, Position, Faculty, Hall, Email, Voter {}

abstract sig EStatus {}
one sig HasNotStarted, HasStarted, HasEnded extends EStatus {}

abstract sig ifCommute {}
one sig DoesCommute, DoesntCommute extends ifCommute {}

abstract sig ifGraduate {}
one sig isGraduate, IsntGraduate extends ifGraduate {}

abstract sig VStatus {}
one sig HasVoted, HasntVoted extends VStatus {}

//UWIVOTES - Closed System Rep
sig uwiVotes {
    //Relations
    election: one Election,
    candidates: set Candidate,
    positions: set Position,
    faculties: set Faculty,
    halls: set Hall,
    voters: set Voter,
    emails: set Email,
    voteStats: set VStatus,

    //Constraints
    candidatePos: candidates -> positions,
    candidateFaculty : candidates -> faculties,
    candidateHall : candidates -> halls,
    voterFaculty : voters -> faculties,
    voterHall: voters -> halls,
    voterStatus: voters -> voteStats

}

//PREDICATES 
pred inv [uv: uwiVotes]{
    //insert invariants
}


//INSTANCES