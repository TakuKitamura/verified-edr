use once_cell::sync::Lazy;
use std::sync::Mutex;

use chrono::prelude::*;
use chrono::Duration;
use std::fs;
use std::fs::OpenOptions;
use std::io::prelude::*;

#[no_mangle]
pub extern "C" fn record_in_edr(
    can_id: u32,
    timestamp: u64,
    speed: u16,
    indicator: u8,
    door: u8,
) -> i32 {
    struct EventData {
        timestamp: chrono::NaiveDateTime,
        can_id: u32,
        speed: f64,
        indicator: u8,
        door: u8,
    }
    static STATIC_EVENT_DATA: Lazy<Mutex<Vec<EventData>>> = Lazy::new(|| Mutex::new(Vec::new()));
    static STATIC_CRASH_TIMESTAMP: Lazy<Mutex<chrono::NaiveDateTime>> =
        Lazy::new(|| Mutex::new(NaiveDateTime::from_timestamp(0, 0)));
    static STATIC_BEFORE_SPEED_INDEX: Lazy<Mutex<usize>> = Lazy::new(|| Mutex::new(0));

    let mut event_data = STATIC_EVENT_DATA.lock().unwrap();
    let mut crash_timestamp = STATIC_CRASH_TIMESTAMP.lock().unwrap();
    let mut before_speed_index = STATIC_BEFORE_SPEED_INDEX.lock().unwrap();

    let sec_part: u64 = timestamp / 1000000000; // 整数部
    let nano_part: u64 = timestamp - (sec_part * 1000000000); // 小数部
    let timestamp = NaiveDateTime::from_timestamp(sec_part as i64, nano_part as u32);

    if can_id == 0x1B4 {
        // speed
        if *before_speed_index == 0 {
            *before_speed_index = event_data.len();
        }

        // 0x10で割る前の値がspeedなので0x10で割る
        let mph_speed: f64 = (speed as f64) / (0x10 as f64);

        event_data.push(EventData {
            can_id: can_id,
            timestamp: timestamp,
            speed: mph_speed,
            indicator: 0,
            door: 0,
        });

        let before_time = event_data[event_data.len() - 1].timestamp;
        // EDRへ書き込み
        // let aaaa = chrono::Duration.secs(5);
        if *crash_timestamp != NaiveDateTime::from_timestamp(0, 0)
            && before_time - *crash_timestamp >= Duration::seconds(5)
        {
            let file_name = "edr.csv";
            let _ = fs::remove_file(file_name);
            let mut file = OpenOptions::new()
                .write(true)
                .append(true)
                .create_new(true)
                .open(file_name)
                .unwrap();

            if let Err(e) = writeln!(file, "EVENT_NAME,TIMESTAMP,VALUE") {
                eprintln!("Couldn't write to file: {}", e);
                return 2;
            }

            // loop event_data
            for i in 0..event_data.len() {
                let event_can_id = event_data[i].can_id;
                if event_can_id == 0x1B4 {
                    // speed
                    if let Err(e) = writeln!(
                        file,
                        "SPEED,{},{}",
                        event_data[i].timestamp, event_data[i].speed,
                    ) {
                        eprintln!("Couldn't write to file: {}", e);
                        return 2;
                    }
                } else if event_can_id == 0x188 {
                    // indicator
                    if let Err(e) = writeln!(
                        file,
                        "INDICATOR,{},{}",
                        event_data[i].timestamp, event_data[i].indicator
                    ) {
                        eprintln!("Couldn't write to file: {}", e);
                        return 2;
                    }
                } else if event_can_id == 0x19b {
                    // door
                    if let Err(e) = writeln!(
                        file,
                        "DOOR,{},{}",
                        event_data[i].timestamp, event_data[i].door
                    ) {
                        eprintln!("Couldn't write to file: {}", e);
                        return 2;
                    }
                }
            }
            return 1;
        }

        let before_speed: f64 = event_data[*before_speed_index].speed;

        let speed_delta: f64 =
        event_data[event_data.len() - 1].speed - before_speed;

        // TODO: 衝突と判定する速度変化を決める
        if speed_delta.abs() >= 10.0 {
            *crash_timestamp = event_data[event_data.len() - 1].timestamp;
        }

        *before_speed_index = event_data.len() - 1;
    } else if can_id == 0x188 {
        // indicator
        event_data.push(EventData {
            can_id: can_id,
            timestamp: timestamp,
            speed: 0.0,
            indicator: indicator,
            door: 0,
        });
    } else if can_id == 0x19B {
        // door
        event_data.push(EventData {
            can_id: can_id,
            timestamp: timestamp,
            speed: 0.0,
            indicator: 0,
            door: door,
        });
    } else {
        return 2;
    }

    return 0;
}
