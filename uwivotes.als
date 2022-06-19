module uwiVotes

//SYSTEM ELEMENTS
sig Election, Candidate, Position, Faculty, Hall, Email {}

abstract sig Status {}
one sig HasNotStarted, HasStarted, HasEnded extends Status {}

abstract sig ifCommute {}
one sig DoesCommute, DoesntCommute extends ifCommute {}

abstract sig ifGraduate {}
one sig isGraduate, IsntGraduate extends ifGraduate {}

//UWIVOTES - Closed System Rep
sig uwiVotes {
    //Relations
    election: one Election,
    electionStatus: one Status,
    candidates: set Candidate,
    positions: set Position,
    faculties: set Faculty,
    halls: set Hall,

    //Constraints
    candidatePos: candidates -> positions,
    candidateFaculty : candidates -> faculties,
    candidateHall : candidates -> halls,
}

//PREDICATES 
pred inv [uv: uwiVotes]{
    //insert invariants
}


//INSTANCES