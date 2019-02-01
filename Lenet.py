from __future__ import absolute_import
from __future__ import division
from __future__ import print_function
import tensorflow as tf
import cv2
import sys
import numpy as np
import os
import glob
from random import shuffle


def multi_label_hot(prediction, threshold=0.5):
    prediction = tf.cast(prediction, tf.float32)
    threshold = float(threshold)
    return tf.cast(tf.greater(prediction, threshold), tf.int64)


# CNN construction
def cnn_model_fn(features, labels, mode):

  # Sort labels
  if not (mode == tf.estimator.ModeKeys.PREDICT):
    blocknum_labels = labels[:]

  # layers
  input_layer = tf.reshape(features["x"], [-1, 56, 56, 3])
  blocknum_conv1 = tf.layers.conv2d(inputs=input_layer, filters=6, kernel_size=[5, 5], padding="same", activation=tf.nn.relu)
  blocknum_pool1 = tf.layers.max_pooling2d(inputs=blocknum_conv1, pool_size=[2, 2], strides=2)
  blocknum_conv2 = tf.layers.conv2d(inputs=blocknum_pool1, filters=16, kernel_size=[5, 5], padding="same", activation=tf.nn.relu)
  blocknum_pool2 = tf.layers.max_pooling2d(inputs=blocknum_conv2, pool_size=[2, 2], strides=2)
  blocknum_pool_flat = tf.reshape(blocknum_pool2, [-1, 14 * 14 * 16])
  blocknum_dense = tf.layers.dense(inputs=blocknum_pool_flat, units=1024, activation=tf.nn.relu)
  blocknum_dropout = tf.layers.dropout(inputs=blocknum_dense, rate=0.4, training=mode == tf.estimator.ModeKeys.TRAIN)
  blocknum_logits = tf.layers.dense(inputs=blocknum_dropout, units=6)

  # Generate predictions (for PREDICT and EVAL mode)
  blocknum_prediction = tf.sigmoid(blocknum_logits)#, axis=1)
  one_hot_prediction = multi_label_hot(blocknum_prediction)
  predictions = {
    "probabilities": tf.sigmoid(blocknum_logits, name="softmax_tensor"),
    "blocknum_classes": one_hot_prediction
  }

  # Return predictions when in PREDICT mode
  if mode == tf.estimator.ModeKeys.PREDICT:
    return tf.estimator.EstimatorSpec(mode=mode, predictions=predictions)

  # Calculate Loss (for both TRAIN and EVAL modes)
  #loss = tf.losses.sparse_softmax_cross_entropy(labels=blocknum_labels, logits=blocknum_logits)
  loss = tf.nn.sigmoid_cross_entropy_with_logits(logits=blocknum_logits, labels=blocknum_labels)
  # loss has the same shape as logits: 1 loss per class and per sample in the batch
  loss = tf.reduce_mean(tf.reduce_sum(loss, axis=1))

  # Configure the Training Op (for TRAIN mode)
  if mode == tf.estimator.ModeKeys.TRAIN:
    #optimizer = tf.train.GradientDescentOptimizer(learning_rate=0.0005)
    optimizer = tf.train.AdamOptimizer(learning_rate=0.0002)
    train_op = optimizer.minimize(loss=loss, global_step=tf.train.get_global_step())
    return tf.estimator.EstimatorSpec(mode=mode, loss=loss, train_op=train_op)

  # Add evaluation metrics (for EVAL mode)
  eval_metric_ops = {"blocknum_accuracy": tf.metrics.accuracy(labels=labels[:], predictions=predictions["blocknum_classes"])}
  return tf.estimator.EstimatorSpec(mode=mode, loss=loss, eval_metric_ops=eval_metric_ops)

 
# Loading the labeled images from the directory
def parse_dataset(train_dataset_size):
    images = []
    labels = []
    images_resized = []

    # loading files from folder
    addrs = glob.glob('objs/*/*/*.png')
    shuffle(addrs)
    st = 0
    unst = 0
    for addr in addrs:
        images.append(cv2.imread(addr))
        label = []
        if 'stable' in addr: # 0 = stable, 1 = unstable
            st += 1
            label.append(0)
            if 'objs/stable/blue/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/stable/blue/'+addr[-18:]):
                  addrs.remove('objs/stable/blue/'+addr[-18:])
            else: label.append(0)
            if 'objs/stable/red/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/stable/red/'+addr[-18:]):
                  addrs.remove('objs/stable/red/'+addr[-18:])
            else: label.append(0)
            if 'objs/stable/green/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/stable/green/'+addr[-18:]):
                  addrs.remove('objs/stable/green/'+addr[-18:])
            else: label.append(0)
            if 'objs/stable/white/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/stable/white/'+addr[-18:]):
                  addrs.remove('objs/stable/white/'+addr[-18:])
            else: label.append(0)
            if 'objs/stable/yellow/'+addr[-18:] in addrs: 
                label.append(1)
                if not(addr == 'objs/stable/yellow/'+addr[-18:]):
                  addrs.remove('objs/stable/yellow/'+addr[-18:])
            else: label.append(0)

        else:
            unst += 1
            label.append(1)
            if 'objs/unstab/blue/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/unstab/blue/'+addr[-18:]):
                  addrs.remove('objs/unstab/blue/'+addr[-18:])
            else: label.append(0)
            if 'objs/unstab/red/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/unstab/red/'+addr[-18:]):
                  addrs.remove('objs/unstab/red/'+addr[-18:])
            else: label.append(0)
            if 'objs/unstab/green/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/unstab/green/'+addr[-18:]):
                  addrs.remove('objs/unstab/green/'+addr[-18:])
            else: label.append(0)
            if 'objs/unstab/white/'+addr[-18:] in addrs: # 0 = not occluded, 1 = occluded
                label.append(1)
                if not(addr == 'objs/unstab/white/'+addr[-18:]):
                  addrs.remove('objs/unstab/white/'+addr[-18:])
            else: label.append(0)
            if 'objs/unstab/yellow/'+addr[-18:] in addrs: 
                label.append(1)
                if not(addr == 'objs/unstab/yellow/'+addr[-18:]):
                  addrs.remove('objs/unstab/yellow/'+addr[-18:])
            else: label.append(0)         

        labels.append(label)

    # resize images to be 56x56
    for image in images:
        resized_image = cv2.resize(image, (56, 56))
        images_resized.append(resized_image) 

    # separate images and labels into train and test sets
    train_images = images_resized[0:train_dataset_size]
    training_labels = labels[0:train_dataset_size]
    test_images = images_resized[train_dataset_size:]
    test_labels = labels[train_dataset_size:]
    files_test = addrs[train_dataset_size:]

    # convert dataset into numpy arrays
    train_data = np.asarray(train_images, np.float32)
    train_labels = np.asarray(training_labels, np.float32)#np.int32)
    eval_data = np.asarray(test_images, np.float32)
    eval_labels = np.asarray(test_labels, np.float32)#np.int32)

    return train_data, train_labels, eval_data, eval_labels, files_test


# MAIN
def train(train_dataset_size):

    tf.logging.set_verbosity(tf.logging.INFO)

    # get training and evaluation data
    train_data, train_labels, eval_data, eval_labels, files_test = parse_dataset(train_dataset_size)

    # Create the Estimator
    cnn = tf.estimator.Estimator(model_fn=cnn_model_fn, model_dir="models/blocknum_cnn")

    # Set up logging for predictions
    # Log the values in the "Softmax" tensor with label "probabilities"
    tensors_to_log = {"probabilities": "softmax_tensor"}
    logging_hook = tf.train.LoggingTensorHook(tensors=tensors_to_log, every_n_iter=50)

    # Train the model
    train_input_fn = tf.estimator.inputs.numpy_input_fn(
        x={"x": train_data},
        y=train_labels,
        batch_size=10,
        num_epochs=None,
        shuffle=True)
    cnn.train(
        input_fn=train_input_fn,
        steps=1000,
        hooks=[logging_hook])

    # Evaluate the model and print results
    eval_input_fn = tf.estimator.inputs.numpy_input_fn(
        x={"x": eval_data},
        y=eval_labels,
        num_epochs=1,
        shuffle=False)
    eval_results = cnn.evaluate(input_fn=eval_input_fn)
    print ('\nAccuracy:')
    print(eval_results)

'''    
    # Use CNN model to get predictions
    prediction_results = cnn.predict(input_fn=eval_input_fn)
    pred_list = list(prediction_results)
    for i in range(len(eval_data)):
        print ('Prediction:')
        print (pred_list[i])
        print ('File name:')
        print (files_test[i])
        print ('Label:')
        print (eval_labels[i])
        print ('\n')
'''    

arg = list(sys.argv)
train_size = arg[-1]
train(int(train_size))



