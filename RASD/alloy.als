/// signatures ///

abstract sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}

sig Email { // NormalUser's email
} {some user: NormalUser | user.email = this }

sig TypeOfViolation { // Segnalation's typeOfViolation
} {(some segnalation: Segnalation | segnalation.typeOfViolation = this) or 
	 (some solution: Solution | solution.typeOfViolation = this)}

sig Location { // a location is identified via latitude and langitude
	latitude:		one Int,
	longitude: one Int
} 

sig Zone { // a zone is identified via the set of its locations
	locations: some Location
}

sig Segnalation { // a location is composed of a location, its type and the normal'user's email who sent it
	location:			one Location,
	typeOfViolation: one TypeOfViolation,
	email: one Email
}

sig Solution { // a solution includes a set of segnalations that occurred in a zone
	segnalations: some Segnalation,
	zone:		one Zone,
	typeOfViolation: one TypeOfViolation
}

abstract sig User { // user can be Municipality or Normal User
	segnalations: set Segnalation
} 

sig Municipality extends User {
	zones:	   some Zone	, // zones that are in the territory of the Municipality
	solutions: set Solution,
	registered: one Bool
}

sig NormalUser extends User { 
	email:			one Email
}

/// ~signatures ///


/// facts ///

// each municipality has all the segnalations sent in its zones
fact municipalityHasItsZonesSegnalations {
	all m: Municipality, s: Segnalation | one z: m.zones |
		s.location in z.locations implies s in m.segnalations
}

// each normal user has the segnalations he sent
fact normalUserHasSegnalationsHeSent {
	all u: NormalUser, s: Segnalation | 
		s.email = u.email implies s in u.segnalations
}

// a municipality receives solutions only if it is registered to safestreet
fact solutionToMunicipalityOnlyIfRegistered {
	all m: Municipality | m.registered = False implies m.solutions = none
}

// two different locations cannot share the same coordinates
fact locationsDiffersForCoordinates {
	no disj l1, l2: Location | l1.latitude = l2.latitude and l1.longitude = l2.longitude
}

// normal users sign up with different emails
fact usersWithDifferentEmail {
	no disj u1, u2: NormalUser | u1.email = u2.email
}

// each segnalation is associated to a single normal user
fact segnalationAssociatedToUniqueUser {
	all segnalation: Segnalation | one user: NormalUser | segnalation in user.segnalations
}

// each segnalation occur in a zone
fact segnalationOccurredInZone {
	all segnalation: Segnalation | one zone: Zone | segnalation.location in zone.locations
}

// each solution is associated to a single municipality
fact solutionAssociatedToUniqueMunicipality {
	all solution: Solution | one municipality: Municipality | solution in municipality.solutions
}

// all segnalations that triggered a solution occurred in the same zone
fact segnalationsInSolutionSameZone {
	all solution:Solution | all segnalation: solution.segnalations
		| some zoneLocation: solution.zone.locations | segnalation.location in zoneLocation
}

// all segnalations that triggered a solution concern the same type of violation
fact segnalationsInSolutionConcernSameTypeOfViolation {
	all solution:Solution | all segnalation: solution.segnalations
		| one tov: TypeOfViolation | segnalation.typeOfViolation = tov and solution.typeOfViolation = tov
}

// the solutions that municipality receives occur in a zone which is in the municipality
fact solutionConcerningMunicipalityZones {
	all municipality: Municipality | all solution: municipality.solutions
		| solution.zone in municipality.zones
}

// each municipality has different zones
fact differentMunicipalityZones {
	no disj m1, m2: Municipality | m1.zones & m2.zones != none
}

// each location belongs to only one Zone
fact locationBelongsToOneZone {
	all location: Location | one  zone: Zone | location in zone.locations
}

// each zone belongs to a municipality
fact zoneBelongsToMunicipality {
	all zone: Zone | one municipality: Municipality | zone in municipality.zones
}

// each segnalation belongs to 0 or 1 solution
fact segnalationBelongsToMax1Solution {
	all segnalation: Segnalation | lone solution: Solution | segnalation in solution.segnalations
}

// each segnalation is associated to a NormalUser
fact segnalationAssociatedToNormalUser {
	all segnalation: Segnalation | one user: NormalUser | segnalation in user.segnalations
}

/// ~facts ///

/// assertions ///

assert SolutionToOneMunicipality { // a solution must be sent to only one municipality
	no disj m1, m2: Municipality | some s: Solution | s in m1.solutions and s in m2.solutions
}

//check SolutionToOneMunicipality

/// ~assertions ///

/// worlds ///
pred world1 {
	(#Municipality > 1) and
	(some m: Municipality | m.registered = False) and
	(#Segnalation > 0)
}

pred world2 {
	(#Municipality = 2) and
	(#NormalUser >=  2)  and
	(all m: Municipality | m.solutions != none)
}

run world1 for 3

/// ~worlds ///
