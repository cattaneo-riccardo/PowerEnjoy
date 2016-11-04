open util/boolean

// Car, User

sig Car {
	id: Int,
	available: Bool,
	location: Location,
	unlocked: Bool,
	battery_level: Int
} {
	int id>0
	battery_level >= 0
	battery_level <= 100
}

sig User {
	credential: Credential,
	password: Password,
	payment_info: Payment_Info,
	location: Location
}
sig Credential {}
sig Password {}
sig Payment_Info {}

// Reservation, Ride

sig Reservation {
	user: User,
	car: Car,
	start_area: Safe_Area,
	start_time: Time,
	expired: Bool,
	ride: lone Ride
}

sig Ride {
	reservation: Reservation,
	passengers: Int, 
	pickup_time: Time,
	release_time: lone Time,
	release_battery_level: lone Int,
	release_area: lone Safe_Area
} {
	passengers >= 1
	passengers <= 4
	release_battery_level >= 0
	release_battery_level <= 100
}

// Time and CurrentTime

sig Time {
	day: Int,
	hour: Int,
	minute: Int
} {
	day >= 0
	day =< 365
	hour >= 0
	hour =< 23
	minute >= 0
	minute =< 59
}

sig CurrentTime extends Time {}

// Location, Areas

sig Location {
	latitude: Int, 
	longitude: Int 
}
sig Area {
	center: Location,
	radius: Int
} {
	radius > 0 
}
sig Safe_Area extends Area {}
sig Special_Safe_Area extends Safe_Area {}

// ----------- Functions ------------

// ----------- Predicates -----------

// Returns true if t - t' <= 1h

pred isLessThanOneHourAhead[t, t': Time] {
	areEqual[t, t']
	or
	(t.day = t'.day
		implies (
			(t.hour = t'.hour and t.minute > t'.minute)
			or
			(t.hour = add[t'.hour,1] and add[sub[60, t'.minute], t.minute] < 60)
		)
		else (
			(t.day = add[t'.day, 1] and t.hour = 0 and t'.hour = 23 and add[sub[60, t'.minute], t.minute] < 60)
		)
	)
}

// Returns true if t >= t'

pred comesAfterOrEqual[t, t': Time] {
	t.day = t'.day
	implies (
		t.hour = t'.hour
		implies t.minute >= t'.minute
		else t.hour >= t'.hour
	)
	else t.day >= t'.day
}

// Returns true if t == t'

pred areEqual[t, t': Time] {
	t.day = t'.day and t.hour = t'.hour and t.minute = t'.minute
}

// Returns true if the max distance between latitudes and longitudes is 5

pred isNear[l, l': Location] {
	(l.latitude >= l'.latitude implies 
		sub[l.latitude, l'.latitude] <= 5
	else
		sub[l'.latitude, l.latitude] <= 5)
	and
	(l.longitude >= l'.longitude implies 
		sub[l.longitude, l'.longitude] <= 5
	else
		sub[l'.longitude, l.longitude] <= 5)
}

// Reservation r is open <=> r is expired and "it has not a ride yet or its ride has no release_time"

pred isOpen[r: Reservation] {
	r.expired = False and (
		no r.ride
		or
		no r.ride.release_time
	)
}

// ----------- Facts -------------

// There's only a current time

fact currentTimeForeverAlone {
	#CurrentTime = 1
}

// CurrentTime is after all the times in the model

fact currentTimeIsAlwaysAhead {
	all t: Time |
		all ct: CurrentTime |
			comesAfterOrEqual[ct, t]
}

// Each credential/password/payment info is used for a user

fact eachCredentialCorrespondToAUser {
	all c: Credential |
		some u: User |
			u.credential = c
}

fact eachPasswordCorrespondToAUser {
	all p: Password |
		some u: User |
			u.password = p
}

fact eachPaymentInfoCorrespondToAUser {
	all pi: Payment_Info |
		 some u: User |
			u.payment_info = pi
}

// Different users <=> different credentials

fact noUsersWithSameCredentials {
	all u1, u2: User |
		u1 != u2
		iff
		u1.credential != u2.credential
}

// Different cars <=> different IDs

fact noCarsWithSameIDs {
	all c1, c2: Car |
		c1 != c2
		iff
		c1.id != c2.id
}

// There can't be two reservations made by the same user both open
// COMMENT: Actually it's possible that a user makes a wrong reservation and he lets it expires, while he makes another one
/*
fact noConsecutiveReservations {
	all r, r': Reservation | (
		r.user = r'.user
		implies not (
			isOpen[r] and isOpen[r']
		)
	)
}*/

// There can't be two reservations r1 and r2 for the same car overlapping.

fact carsCanBeReservedByOneUserAtOnce {
	all c: Car | (
		all r, r': Reservation | (
			(r.car = c and r'.car = c and r != r' and comesAfterOrEqual[r'.start_time, r.start_time])
			implies (
					(some r.ride and some r.ride.release_time and comesAfterOrEqual[r'.start_time, r.ride.release_time])
					or
					(r.expired = True and not isLessThanOneHourAhead[r'.start_time, r.start_time])
			)
		)
	)
}

// A car is available if it has no reservations open.

fact carAvailableCondition {
	all c: Car |
		c.available = True
		iff
		(all res: Reservation |
			res.car = c
			implies
			isOpen[res]
		)
}

// A reservation is expired if there's is not a ride whose pickup_time is less than one hour after the 
//    reservation start_time.

fact carExpiredCondition {
	all res: Reservation |
		res.expired = True
		iff
		(all currentTime: CurrentTime |
			not isLessThanOneHourAhead[currentTime, res.start_time]
		)
		and
		no res.ride
}

// The pickup time of a ride should be in one hour from its reservation start_time

fact pickupTimeConstraint {
	all rid: Ride | (
		isLessThanOneHourAhead[rid.pickup_time, rid.reservation.start_time]
	)
}

// If a reservation has a ride, then that ride has that reservation.

fact ridesAndReservationRelation {
	all res: Reservation | (
		some res.ride
		implies
		res = res.ride.reservation
	)
	/*
	(all rid: Ride |
		some res: Reservation |
			rid.reservation = res and res.ride = rid)
	(all res, res': Reservation |
		res != res'
		implies
		res.ride != res'.ride)*/
}

// A car is unlocked if there's a reservation not expired between a user and that car,
//    such user is near it and
//    he hasn't finished the ride (the ride associated with that reservation 
//    doesn't have a release_time).

fact carUnlockedConstraint {
	all c: Car | (
		c.unlocked = True
		iff
		some r: Reservation | (
			r.car = c and isOpen[r] and isNear[c.location, r.user.location]
		)
	)
/*
	all c: Car | (
		c.unlocked = True
		iff (
			some res: Reservation | (
				res.car = c and res.expired = False and
				some u: User | (
					res.user = u and
					isNear[u.location, c.location] and
					(no res.ride or no res.ride.release_time)
				)
			)
		)
	)
*/
}

// release_time is always after pickup_time

fact releaseTimeIsAfterPickupTime {
	all rid: Ride | (
		no rid.release_time
		or
		comesAfterOrEqual[rid.release_time, rid.pickup_time]
	)
}

// ------------- Assertions ---------------

// car available => car locked

// car unlocked => car not available

// ------------ Show world! --------------

pred show {
	#User = 1
	#Car = 2
	#Reservation = 3
	some c: Car | c.unlocked = True
	some c: Car | c.unlocked = False
}

pred checkUnlocked {
	
}

//run show for 8 Int
run show for 8 Int
//check currentTimeIsAlwaysAhead for 8 Int
