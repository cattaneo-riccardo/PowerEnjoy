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
	battery_level <= 10
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
	release_battery_level <= 10
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

//A car can be released plugged only if it is released in a Special Safe Area
fact pluggedOnlyInSafeArea{
	all rid: Ride |(
		rid.release_plugged=True
		implies
		(rid.release_area in Special_Safe_Area)
	)
}

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
//A user can reserve a car only if it has a battery level grater than 80%
fact carReservableCondition {
	all r: Reservation | (
		(no r.ride and r.expired=False)
		implies
		r.car.battery_level>8
	)
}
// A car is available if it has no reservations open and has enough battery
fact carAvailableCondition {
	all c: Car |
		c.available = True
		iff(
		(no res: Reservation |
			res.car = c and isActive[res])
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

//If a car is locked and not plugged to a power grid, its battery level is the same as it has been left after last ride
fact batteryLevelConstraint{
	all res: Reservation | (
		(no res': Reservation | (res!=res' and res.car=res'.car and comesAfterOrEqual[res'.start_time, res.start_time]))
		implies (
			(res.ride.release_plugged=False and res.car.location=res.ride.release_area.location)
			implies
				res.ride.release_battery_level = res.car.battery_level
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


fact finalDischargedCostCalculation {
	all res: Reservation | (
		(one res.ride.release_time and res.ride.passengers>2)         
		implies(			 //Enabled to 10% discount
			(res.expired = False and res.ride.release_battery_level>=5)
			implies(		 //Enabled to 10%+20% discount
				 (res.ride.release_plugged = True)
				implies(  //Enablet to 10%+20%+30% discount
					res.final_discharged_cost=div[mul[res.current_cost, 2],5]
				)
				else(       //Enabled to 10%+20% discount
					res.final_discharged_cost=div[mul[res.current_cost, 7],10]
				)
			)
			else(
				(res.ride.release_plugged = True)
				implies(  //Enablet to 10%+30% discount
					res.final_discharged_cost=div[mul[res.current_cost, 3],5]
				)
				else(       //Enabled to 10% discount, but 30% extra charging
					(isFarFromSpecialSafeArea[res.ride.release_area] and res.ride.release_battery_level<3)
					implies (
						res.final_discharged_cost=div[mul[res.current_cost, 6],5]
					)
					else(
						res.final_discharged_cost=div[mul[res.current_cost, 9],10]
					)
				)
			)
		)
		else(
			(res.expired = False and res.ride.release_battery_level>=5)
			implies(		 //Enabled to 20% discount
				 (res.ride.release_plugged = True)
				implies(  //Enablet to 20%+30% discount
					res.final_discharged_cost=div[res.current_cost,2]
				)
				else(       //Enabled to 20% discount
					res.final_discharged_cost=div[mul[res.current_cost, 4],5]
				)
			)
			else(
				(res.ride.release_plugged = True)
				implies(  //Enablet to 30% discount
					res.final_discharged_cost=div[mul[res.current_cost, 7],10]
				)
				else(       //There are no discounts
					(isFarFromSpecialSafeArea[res.ride.release_area] and res.ride.release_battery_level<3)
					implies ( //Extra-charging of 30%
						res.final_discharged_cost=div[mul[res.current_cost, 13],10]
					)
					else( // No discounts orr extra-charging
						res.final_discharged_cost=res.current_cost
					)
				)
			)
		)
	)
}

// ------------- Assertions ---------------
assert availabilityAndLockingChecking {
	all c: Car | ((c.available = True implies c.unlocked = False)			  // car available => car locked
						and (c.unlocked = True implies c.available = False))	  // car unlocked => car not available
}

// reservation expired => no ride
assert expiredEntailsNoRide {
	all r: Reservation | r.expired = True implies (no r.ride and r.final_discharged_cost=10)
}

// reservation active => car not available and there aren't any other active reservations for that car
assert activeEntailsNotAvailable {
	all r: Reservation | isActive[r] implies (r.car.available = False
															and no r': Reservation | r'!=r and isActive[r'] and r.car=r'.car)
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
	#Reservation = 2
	#Ride=1
	#Car=1	
	some r: Reservation | (one r.ride.release_time) 
//	all rid: Ride | all ct: CurrentTime | rid.release_time!=ct
//	some c: Car | c.unlocked = False

}

//run show for 8 Int
//check availabilityAndLockingChecking for 8 Int
//check activeEntailsNotAvailable for 8 Int
check expiredEntailsNoRide for 8 Int
//check activeEntailsNotAvailable for 7 Int
//check falseByPurpose for 8 Int
