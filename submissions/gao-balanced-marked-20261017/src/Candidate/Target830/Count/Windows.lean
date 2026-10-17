import Candidate.Target830.Count.Availability
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace OAI.SevenEighths.Target830.Count
noncomputable section

def window0 : Window where
  plane := .oldWeak
  deltaLo := 111/256
  deltaHi := 57/128
  pLo := 63/128
  bounds := by norm_num

def window1 : Window where
  plane := .oldWeak
  deltaLo := 57/128
  deltaHi := 459/1024
  pLo := 127/256
  bounds := by norm_num

def window2 : Window where
  plane := .PR60
  deltaLo := 57/128
  deltaHi := 459/1024
  pLo := 255/512
  bounds := by norm_num

def window3 : Window where
  plane := .PR60
  deltaLo := 459/1024
  deltaHi := 231/512
  pLo := 127/256
  bounds := by norm_num

def window4 : Window where
  plane := .PR62
  deltaLo := 231/512
  deltaHi := 465/1024
  pLo := 127/256
  bounds := by norm_num

def window5 : Window where
  plane := .A
  deltaLo := 465/1024
  deltaHi := 117/256
  pLo := 127/256
  bounds := by norm_num

def window6 : Window where
  plane := .C
  deltaLo := 117/256
  deltaHi := 237/512
  pLo := 63/128
  bounds := by norm_num

def window7 : Window where
  plane := .C
  deltaLo := 237/512
  deltaHi := 15/32
  pLo := 63/128
  bounds := by norm_num

def window8 : Window where
  plane := .C
  deltaLo := 15/32
  deltaHi := 123/256
  pLo := 63/128
  bounds := by norm_num

def window9 : Window where
  plane := .C
  deltaLo := 123/256
  deltaHi := 63/128
  pLo := 63/128
  bounds := by norm_num

end
end OAI.SevenEighths.Target830.Count
