open util/boolean

// Car, User

sig Car {
	id: Int,
	available: Bool,
	location: Location,
	unlocked: Bool,
	battery_level: Int
} {
	id>0
	battery_level >= 0
	battery_level <= 100
}

sig User {
	credential: Credential,
	payment_info: Payment_Info,
	location: Location
}
sig Credential {}

sig Payment_Info {}

// Reservation, Ride

sig Reservation {
	user: User,
	car: Car,
	start_area: Safe_Area,
	start_time: Time,
	current_cost: Int,
	final_discharged_cost: lone Int,
	expired: Bool,
	ride: lone Ride
} {
	current_cost >= 0
	final_discharged_cost >= 0
}

sig Ride {
	reservation: Reservation,
	passengers: Int, 
	pickup_time: Time,
	release_time: lone Time,
	release_battery_level: lone Int,
	release_area: lone Safe_Area,
	release_plugged: lone Bool
} {
	passengers >= 1
	passengers <= 4
	release_battery_level >= 0
	release_battery_level <= 100
	not areEqual[pickup_time, release_time]
}

// Time and CurrentTime

sig Time {
	hour: Int,
	minute: Int
} {
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
//	radius: Int
} {
//	radius > 0 
}
sig Safe_Area extends Area {}
sig Special_Safe_Area extends Safe_Area {}

/* ----------- Functions ------------ */
fun minutesDiff[t, t': Time]:Int {
	t.minute>t'.minute
	implies
		sub[t.minute, t'.minute]
	else
		sub[t'.minute, t.minute]
}

fun hoursDiff[t, t': Time]: Int {
	t.hour>=t'.hour
	implies(
		sub[t.hour, t'.hour]
	) else (
		sub[t'.hour, t.hour]
	)
}

//Return the cost for a ride from time t to time t'
fun cost[t, t': Time]: Int {
		t.hour = t'.hour
		implies (
			minutesDiff[t, t']
		)
		else (
			t.hour>t'.hour
			implies(
				add[add[sub[60, t'.minute], mul[sub[hoursDiff[t,t'], 1], 60]], t.minute]   //(60-t'.minute) + (t'.hour-t.hour-1)*60 + t.minute
			)
			else(
				add[add[sub[60, t.minute], mul[sub[hoursDiff[t,t'], 1], 60]], t'.minute]   //(60-t.minute) + (t.hour-t'.hour-1)*60 + t'.minute			
			)
		)
}
// ----------- Predicates -----------

// Returns true if t == t'
pred areEqual[t, t': Time] {
	t.hour = t'.hour and t.minute = t'.minute
}

// Returns true if t - t' <= 1h
pred isLessThanOneHourAhead[t, t': Time] {
	areEqual[t, t']
	or
		(t.hour = t'.hour and t.minute > t'.minute)
	or
		(t.hour = add[t'.hour,1] and add[sub[60, t'.minute], t.minute] < 60)
}

// Returns true if t >= t'
pred comesAfterOrEqual[t, t': Time] {
		t.hour = t'.hour
		implies t.minute >= t'.minute
		else t.hour >= t'.hour
}

// Returns true if the max distance between latitudes and longitudes is 5
pred isNear[l, l': Location] {
	(l.latitude >= l'.latitude implies 
		sub[l.latitude, l'.latitude] <= 4
	else
		sub[l'.latitude, l.latitude] <= 4)
	and
	(l.longitude >= l'.longitude implies 
		sub[l.longitude, l'.longitude] <= 4
	else
		sub[l'.longitude, l.longitude] <= 4)
}

pred isFarFromSpecialSafeArea[area: Safe_Area] {
			all ssa: Special_Safe_Area |(
			(int ssa.center.latitude >= int area.center.latitude
			implies 
				sub[ssa.center.latitude, area.center.latitude] > 15
			else
				sub[area.center.latitude, ssa.center.latitude] > 15
			)
			and
			(int ssa.center.longitude >= int area.center.longitude implies 
				sub[ssa.center.longitude, area.center.longitude] > 15
			else
				sub[area.center.longitude, ssa.center.longitude] > 15)
	)
}
// Reservation r is open <=> r is not expired and "it has not a ride yet or its ride has no release_time"
pred isActive[r: Reservation] {
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

//There are no different Time with the same time
/*fact alwaysDifferent {
	all t, t': Time | t!=t' implies (not areEqual[t, t'])
}*/

// CurrentTime is after all the times in the model
fact currentTimeIsAlwaysAhead {
	all t: Time |
		all ct: CurrentTime |
			comesAfterOrEqual[ct, t]
}

// Each credential/password/payment info is used for a user
fact eachCredentialCorrespondToAUser {
	User.credential=Credential
}

fact eachPaymentInfoCorrespondToAUser {
	User.payment_info=Payment_Info
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

// If a ride has a reservation, then that reservation has that ride.
fact ridesAndReservationRelation {
	all rid: Ride | (
		rid = rid.reservation.ride
	) and
	all res: Reservation | (
		one res.ride 
		implies
			res=res.ride.reservation
	)
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

// A car is available if it has no reservations open and has enough battery
fact carAvailableCondition {
	all c: Car |
		c.available = True
		iff(
		(no res: Reservation |
			res.car = c and isActive[res])
		 and  c.battery_level>80
		)
}

// A reservation is expired if there's is not a ride whose pickup_time is less than one hour after the 
//    reservation start_time.
fact reservationExpiredCondition {
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

// release_time is always after pickup_time
fact releaseTimeIsAfterPickupTime {
	all rid: Ride | (
		no rid.release_time
		or
		comesAfterOrEqual[rid.release_time, rid.pickup_time]
	)
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
			r.car = c and isActive[r] and isNear[c.location, r.user.location]
		)
	)
}

//If there is a release time, there are also a release release_battery and a release_area
fact releaseInfoConstraint{
	all rid: Ride| (
		(some rid.release_time
		iff
		some rid.release_battery_level) and 
		(some rid.release_area 
		iff
		some rid.release_time) and 
		(some rid.release_time
		 iff
		some rid.release_plugged)
	)
}

fact feeConstraint {
	all r: Reservation | (
		r.expired = True
		implies
		r.current_cost = 10 and r.final_discharged_cost = 10
	)
}

//The actual cost of a reservation is proportional to minutes spent in the car
fact costOfAReservationConstraint {
	all res: Reservation | (
		res.expired = False
		implies (
			no res.ride
			implies
				res.current_cost=0
			else(
				no res.ride.release_time
				implies(
					all ct : CurrentTime |
						res.current_cost=cost[ct, res.ride.pickup_time]
				)
				else
					res.current_cost=cost[res.ride.release_time, res.ride.pickup_time]
			)
		)
	)
}

//Passengers discount of 10%
fact passengersDiscount{
	all res: Reservation | (
		res.expired = False and one res.ride.release_time and res.ride.passengers>2
		implies(
			res.final_discharged_cost=div[mul[res.current_cost, 9],10]
		)
	)
}

//Non-empty battery discount of 20%
fact nonEmptyBatteryDiscount{
	all res: Reservation | (
		res.expired = False and res.ride.release_battery_level>=50
		implies(
			res.final_discharged_cost=div[mul[res.current_cost, 4],5]
		)
	)
}

//Car released charging discount of 30%
fact chargingDiscount{
	all res: Reservation | (
	res.expired = False and (res.ride.release_area in Special_Safe_Area) and res.ride.release_plugged = True
		implies(
			res.final_discharged_cost=div[mul[res.current_cost, 7],10]
		)
	)
}

//Car released far and with low battery extra-charging of 30%
fact lowBatteryExtraFee{
	all res: Reservation | (
		res.expired = False and res.ride.release_battery_level<20 and isFarFromSpecialSafeArea[res.ride.release_area]
		implies(
			res.final_discharged_cost=div[mul[res.current_cost, 13],10]
		)
	)
}
// ------------- Assertions ---------------

// car available => car locked

assert availableEntailsLocked {
	all c: Car | c.available = True implies c.unlocked = False
}

// car unlocked => car not available

assert unlockedEntailsNotAvailable {
	all c: Car | c.unlocked = True implies c.available = False
}

// reservation expired => no ride

assert expiredEntailsNoRide {
	all r: Reservation | r.expired = True implies no r.ride
}

// reservation active => car not available

assert activeEntailsNotAvailable {
	all r: Reservation | isActive[r] implies r.car.available = False
}

// FALSE

assert falseByPurpose {
	all r: Reservation | r.start_time = r.ride.release_time
	or
	all ride: Ride |  all ct: CurrentTime| ride.release_time=ct
}

// ------------ Show world! --------------

pred show {
	#User = 1
	#Reservation = 1
	some r: Reservation | (r.ride.release_battery_level>=50) 
	some c: Car | c.available = True
//	some c: Car | c.unlocked = False

}

run show for 8 Int
//check availableEntailsLocked for 7 Int
//check unlockedEntailsNotAvailable for 7 Int
//check expiredEntailsNoRide for 7 Int
//check activeEntailsNotAvailable for 7 Int
//check falseByPurpose for 8 Int
